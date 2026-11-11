-- Prove2me | Theorems.Thm_UnitalMIP_theorem_3_1
-- name    : UnitalMIP.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:39:42.681852+00:00
-- url     : https://prove2.me/theorems/03284e4d-a3fe-44d8-938b-70470c5c8afb
-- title:
--   Theorem 3.1 — finite-copy approximation: $D$ copies suffice up to $C\varepsilon$
-- statement:
--   There are absolute constants $C,\gamma>0$ such that the following holds. Let $\psi\in M_2\otimes M_2$ be a state with $\psi_A=\psi_B=\mathbb 1/2$ and $\rho_{\max}(\psi)<1$. There is a constant $\alpha_\psi\in[0,1)$, depending only on $\psi$, such that for every game $G$ with $t:=\max\{|\mathcal A|,|\mathcal B|\}$ and every $0<\varepsilon<1/10$, with
--
--   $$
--   k=\Bigl\lceil\Bigl(\frac{C(\log(2t))^2}{(1-\alpha_\psi)\varepsilon^{14}}\Bigr)^{1/\gamma}\Bigr\rceil,\qquad D=\Bigl\lceil Ck^{64}\max\Bigl\{\frac{t^2}{\varepsilon^2},\frac{t}{\varepsilon^6}\Bigr\}\Bigr\rceil,
--   $$
--
--   for every $n\ge1$ and every local POVM strategy $\mathcal A,\mathcal B$ on $\psi^{\otimes n}$ there is a local POVM strategy $\mathcal A^\sharp,\mathcal B^\sharp$ on $\psi^{\otimes D}$ with $\mathrm{Val}^{\psi^{\otimes D}}_G(\mathcal A^\sharp,\mathcal B^\sharp)\ge\mathrm{Val}^{\psi^{\otimes n}}_G(\mathcal A,\mathcal B)-C\varepsilon$.
--
--   The number of copies needed depends only on the answer-alphabet size and the accuracy, which makes the value approximable in nondeterministic exponential time.
--
--   **Formalization Note** Quantifier order as printed ($C,\gamma$ before $\psi$; $\alpha_\psi$ after $\psi$, before the game). Ceilings are `Nat.ceil`; $\log$ is natural.
--
--   Differences from the source:
--   - encoding: $\psi^{\otimes n}$ → `tensorPow ψ n`: the same operator with Alice's $n$ registers collected first; reason: a permutation of tensor factors; Alice holds the first qubit of every copy, as in the source
--   - encoding: $\mathrm{Tr}[(A^x_a\otimes(B^y_b)^T)\psi]$ in the value (16), (22) → the real part of this trace; reason: the trace is real for the positive semidefinite families and states to which the source applies the formula
--   - generalization: the §1.1 standing assumption (“Throughout, let ψ be a fixed two-qubit state … and assume that its entries are computable in polynomial time”, p.4) → any two-qubit density matrix ψ with the stated properties, with no computability hypothesis; reason: the statement is purely analytic and holds for every such state; it specializes to the source's claim on every computable ψ
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Theorem 3.1, p.26

import Mathlib
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals
import Definitions.Def_UnitalMIP_rhoMax
import Definitions.Def_UnitalMIP_omegaInf

open scoped Matrix

namespace UnitalMIP

/-- **Theorem 3.1** (Finite-copy approximation; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.26). There are absolute constants `C, γ > 0`
such that: for every `ψ ∈ M₂ ⊗ M₂` with `ψ_A = ψ_B = 𝟙/2` and `ρmax(ψ) < 1` there is a constant
`α_ψ ∈ [0, 1)` such that, for every game with `t := max{|𝒜|, |ℬ|}` and every `0 < ε < 1/10`, with
`k = ⌈(C (log(2t))² / ((1 − α_ψ) ε¹⁴))^{1/γ}⌉` and `D = ⌈C k⁶⁴ max{t²/ε², t/ε⁶}⌉`, for every
`n ≥ 1` and every local POVM strategy `𝒜, ℬ` on `ψ^{⊗n}` there is a local POVM strategy `𝒜♯, ℬ♯` on
`ψ^{⊗D}` with `Val^{ψ^{⊗D}}_G(𝒜♯, ℬ♯) ≥ Val^{ψ^{⊗n}}_G(𝒜, ℬ) − Cε`.

**Formalization Note** Quantifier order as printed: `C`, `γ` before `ψ`; `α_ψ` after `ψ` and before the
game. The ceilings are `Nat.ceil`; `log` is the natural logarithm. `ψ` is a density matrix. -/
theorem theorem_3_1 :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ (ψ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ), QAlgorithms.IsDensityMatrix ψ →
        HasMaxMixedMarginals ψ → rhoMax ψ < 1 →
      ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : MIPRE.Game X Y A B) (ε : ℝ), 0 < ε → ε < 1 / 10 →
        let t : ℝ := (max (Fintype.card A) (Fintype.card B) : ℝ)
        let k : ℕ := ⌈(C * Real.log (2 * t) ^ 2 / ((1 - α) * ε ^ 14)) ^ (1 / γ)⌉₊
        let D : ℕ := ⌈C * (k : ℝ) ^ 64 * max (t ^ 2 / ε ^ 2) (t / ε ^ 6)⌉₊
        ∀ (n : ℕ), 1 ≤ n →
        ∀ (SA : X → MIPRE.POVM A (Fin n → Fin 2)) (SB : Y → MIPRE.POVM B (Fin n → Fin 2)),
        ∃ (SA' : X → MIPRE.POVM A (Fin D → Fin 2)) (SB' : Y → MIPRE.POVM B (Fin D → Fin 2)),
          val G (tensorPow ψ n) (povmMats SA) (povmMats SB) - C * ε ≤
            val G (tensorPow ψ D) (povmMats SA') (povmMats SB') := by sorry

end UnitalMIP
