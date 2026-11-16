-- Prove2me | Theorems.Thm_UnitalMIP_Supplement_theorem_4_11
-- name    : UnitalMIP.Supplement.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:16:13.289807+00:00
-- url     : https://prove2.me/theorems/a3e9fce0-37f6-41fe-a8a2-15e729dba071
-- title:
--   Theorem 4.11 — Hermitian low-degree approximation in the normalized Schatten 4-norm
-- statement:
--   There are absolute constants $b,\gamma>0$ with the following property. Let $d_0,n\ge1$ and let $S$ be a Hermitian operator in $M_{d_0}\otimes M_{2^n}$. For every integer $k\ge1$ there is a Hermitian operator $R$ with the low-degree expansion
--
--   $$
--   R=\sum_{|\alpha|\le k}\widehat R(\alpha)\otimes P_\alpha,\qquad \widehat R(\alpha)\in M_{d_0},
--   $$
--
--   such that
--
--   $$
--   \|S-R\|_4\le 2\,\bigl\|S-(\mathbb 1_{d_0}\otimes\mathcal T_{bk^{-\gamma}})(S)\bigr\|_4 .
--   $$
--
--   Here $P_\alpha$ ranges over the $n$-qubit Pauli strings, $|\alpha|$ is the Pauli weight, $\|\cdot\|_4$ is the normalized Schatten 4-norm with trace $\tau_{d_0}\otimes\tau_{2^n}$, and $\mathcal T_u=D_u^{\otimes n}$ is the $n$-qubit depolarizing semigroup, $D_u=\Pi+e^{-u}(\mathrm{id}-\Pi)$ with $\Pi(X)=\tau_2(X)\mathbb 1$, acting only on the qubit factor. The constants $b$ and $\gamma$ do not depend on $d_0$, $n$, $S$ or $k$.
--
--   The theorem says that the distance in the 4-norm from a Hermitian operator to the operators of Pauli degree at most $k$ is controlled, up to the factor $2$, by how much the operator moves under depolarization for time $bk^{-\gamma}$. It is the step of the paper that turns smoothed measurement operators into low-degree ones (Theorem 3.3), independently of the ancilla dimension $d_0$.
--
--   **Formalization Note** $M_{d_0}\otimes M_{2^n}$ is indexed by `Fin d0 × (Fin n → Fin 2)`. The map $\mathbb 1_{d_0}\otimes\mathcal T_\theta$ is the published `QAlgorithms.idTensorSuperop` applied to the published `UnitalMIP.depolT θ n`: the depolarizing map is applied to each $d_0$-block. The time $bk^{-\gamma}$ is the real power `b * (k : ℝ) ^ (-γ)`.
--
--   Differences from the source:
--   - encoding: $\mathcal M_{d_0}\otimes\mathcal M_{2^n}$ → complex matrices indexed by `Fin d0 × (Fin n → Fin 2)`; reason: the standard basis of $\mathbb C^{d_0}\otimes(\mathbb C^2)^{\otimes n}$; same operators
--   - encoding: the low-degree expansion $R=\sum_{|\alpha|\le k}\widehat R(\alpha)\otimes P_\alpha$, $\widehat R(\alpha)\in\mathcal M_{d_0}$ → `HasQubitDegreeLE R k`: the $M_{d_0}$-valued Pauli coefficients $\widehat R(\alpha)$ vanish for $|\alpha|>k$ (the subspace $E_{\le k}$ of Definition 4.17); reason: the Pauli strings form a basis, so the expansion is unique and its coefficients are the $\widehat R(\alpha)$ (Definitions 2.7–2.8, Proposition 2.11); same operators
--   - encoding: $\mathcal T^{\otimes n}_{bk^{-\gamma}}$ → `depolT (b * k^(-γ)) n`, i.e. $\mathcal T_\theta=D_\theta^{\otimes n}$ with $\theta=bk^{-\gamma}$; reason: Definition 2.9 sets $\mathcal T_u:=D_u^{\otimes n}$ and the proof (pp.40, 47) sets $\theta=bk^{-\gamma}$; the printed superscript $\otimes n$ marks the $n$-qubit tensor product, not a further power
--   - encoding: "the constants b and γ are independent of d0 and n" → `∃ b γ` quantified before `d0`, `n`, `S` and `k`; reason: the Lean form of absolute constants
--   - encoding: $\|X\|_4=\tau(|X|^4)^{1/4}$ → $\bigl(\mathrm{Re}\,\tau((X^\dagger X)^2)\bigr)^{1/4}$; reason: $|X|^4=(X^\dagger X)^2$ and its normalized trace is a nonnegative real number; same value
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Theorem 4.11, §4.2.1, p.41 (restated p.46, proved p.47)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals
import Definitions.Def_UnitalMIP_pauliString
import Definitions.Def_UnitalMIP_depolT
import Definitions.Def_UnitalMIP_Supplement_nnorm4

open scoped Matrix

namespace UnitalMIP

namespace Supplement

/-- **Theorem 4.11** (Hermitian low-degree approximation in the normalized Schatten 4-norm;
Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*,
arXiv:2609.39318, version of 2026-11-03, sha256 56ebc59e…, §4.2.1, p.41; restated p.46, proved
p.47). There are absolute constants `b, γ > 0` such that for all `d₀, n ≥ 1`, every Hermitian
`S ∈ M_{d₀} ⊗ M_{2ⁿ}` and every integer `k ≥ 1` there is a Hermitian `R = ∑_{|α|≤k} R̂(α) ⊗ P_α`,
`R̂(α) ∈ M_{d₀}`, with `‖S − R‖₄ ≤ 2 ‖S − (1_{d₀} ⊗ 𝒯_{b k^{−γ}})(S)‖₄`.

**Formalization Note** `b` and `γ` are quantified before `d₀`, `n`, `S` and `k`, so they are
independent of them. `M_{d₀} ⊗ M_{2ⁿ}` is indexed by `Fin d₀ × (Fin n → Fin 2)`. The map
`𝒯_θ = D_θ^{⊗n}` (printed `𝒯^{⊗n}_{bk^{−γ}}`; Definition 2.9, p.13; the proof sets
`θ = b k^{−γ}`, p.47) is the published `UnitalMIP.depolT θ n`; `1_{d₀} ⊗ 𝒯_θ` is the published
`QAlgorithms.idTensorSuperop`, which applies `𝒯_θ` to every `d₀`-block (convention (10), p.13).
`‖·‖₄` is the normalized Schatten 4-norm `nnorm4` (trace `τ_{d₀} ⊗ τ_{2ⁿ}`). "Low-degree
expansion" is `HasQubitDegreeLE R k`: the `M_{d₀}`-valued Pauli coefficients `R̂(α)` vanish for
`|α| > k`. -/
theorem theorem_4_11 :
    ∃ b γ : ℝ, 0 < b ∧ 0 < γ ∧
      ∀ (d0 n : ℕ), 1 ≤ d0 → 1 ≤ n →
      ∀ (S : Matrix (Fin d0 × (Fin n → Fin 2)) (Fin d0 × (Fin n → Fin 2)) ℂ), S.IsHermitian →
      ∀ k : ℕ, 1 ≤ k →
        ∃ R : Matrix (Fin d0 × (Fin n → Fin 2)) (Fin d0 × (Fin n → Fin 2)) ℂ,
          R.IsHermitian ∧ HasQubitDegreeLE R k ∧
          nnorm4 (S - R) ≤
            2 * nnorm4 (S - QAlgorithms.idTensorSuperop (R := Fin d0)
              (depolT (b * (k : ℝ) ^ (-γ)) n) S) := by sorry

end Supplement

end UnitalMIP
