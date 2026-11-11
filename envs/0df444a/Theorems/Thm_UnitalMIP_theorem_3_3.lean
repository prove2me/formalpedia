-- Prove2me | Theorems.Thm_UnitalMIP_theorem_3_3
-- name    : UnitalMIP.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:39:55.125239+00:00
-- url     : https://prove2.me/theorems/0182b1f6-9e54-41b8-bfbb-e5a1e02ddbdc
-- title:
--   Theorem 3.3 — positive low-degree approximation of smoothed strategies
-- statement:
--   There are absolute constants $C,\gamma$ with the following property. Let $n\ge1$, $t\ge2$, $w>0$, $\eta\in(0,1)$; fix a game $G$ with $t=\max\{|\mathcal A|,|\mathcal B|\}$, a two-qubit state $\psi$ with $\psi_A=\psi_B=\mathbb 1/2$, and local POVM strategies $\mathcal A,\mathcal B$ on $(\mathbb C^2)^{\otimes n}$. Let $k$ be an integer greater than $\bigl(C\log(2t)/(w\eta^4)\bigr)^{1/\gamma}$. Then there are smoothing times $u_x,v_y\in[w,2w]$ and block operators $Q^x=\sum_a|a\rangle\otimes Q^x_a$, $R^y=\sum_b|b\rangle\otimes R^y_b$ such that
--
--   1. every $Q^x_a$ and $R^y_b$ has Pauli degree at most $k$;
--   2. $\|(Q^x)^\dagger Q^x-\mathbb 1\|_2\le(2+\eta)\eta$ and $\|(R^y)^\dagger R^y-\mathbb 1\|_2\le(2+\eta)\eta$ for all $x,y$;
--   3. the approximate strategies $\mathcal Q^x=((Q^x_a)^\dagger Q^x_a)_a$, $\mathcal R^y=((R^y_b)^\dagger R^y_b)_b$ satisfy
--   $$
--   \bigl|\mathrm{Val}_G(\mathcal Q,\mathcal R)-\mathrm{Val}_G(\mathcal A^{(u)},\mathcal B^{(v)})\bigr|\le15\eta .
--   $$
--
--   This is one of the paper's two techniques of independent interest: positivity is kept by passing to block operators $Q$ and the PSD operators $Q_a^\dagger Q_a$.
--
--   **Formalization Note** $(Q^x)^\dagger Q^x=\sum_a(Q^x_a)^\dagger Q^x_a$; $\|\cdot\|_2$ is the normalized Schatten 2-norm; values are on $\psi^{\otimes n}$, the approximate one by formula (22).
--
--   Differences from the source:
--   - reading: “absolute constants C, γ” → constants with $C>0$ and $\gamma>0$; reason: Theorem 3.1 and Figure 2 state the same $\gamma$ as positive; requiring positivity is the stronger existential
--   - encoding: Pauli degree at most $k$ ($\deg(0)=-\infty$) → every Pauli coefficient $\hat F(\alpha)$ with $|\alpha|>k$ vanishes; reason: the same condition, including the zero operator
--   - encoding: $\psi^{\otimes n}$ → `tensorPow ψ n`: the same operator with Alice's $n$ registers collected first; reason: a permutation of tensor factors; Alice holds the first qubit of every copy, as in the source
--   - encoding: $\mathrm{Tr}[(A^x_a\otimes(B^y_b)^T)\psi]$ in the value (16), (22) → the real part of this trace; reason: the trace is real for the positive semidefinite families and states to which the source applies the formula
--   - generalization: the §1.1 standing assumption (“Throughout, let ψ be a fixed two-qubit state … and assume that its entries are computable in polynomial time”, p.4) → any two-qubit density matrix ψ with the stated properties, with no computability hypothesis; reason: the statement is purely analytic and holds for every such state; it specializes to the source's claim on every computable ψ
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Theorem 3.3, p.27

import Mathlib
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals
import Definitions.Def_UnitalMIP_rhoMax
import Definitions.Def_UnitalMIP_omegaInf
import Definitions.Def_UnitalMIP_depolT
import Definitions.Def_UnitalMIP_pauliString

open scoped Matrix

namespace UnitalMIP

/-- **Theorem 3.3** (Low-degree approximation; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.27). There are absolute constants `C, γ` such
that: for `n ≥ 1`, `t ≥ 2`, `w > 0`, `η ∈ (0, 1)`, a game with `t = max{|𝒜|, |ℬ|}`, a two-qubit state
`ψ` with `ψ_A = ψ_B = 𝟙/2`, local POVM strategies `𝒜`, `ℬ` on `(ℂ²)^{⊗n}`, and an integer
`k > (C log(2t)/(w η⁴))^{1/γ}`, there are smoothing times `u_x, v_y ∈ [w, 2w]` and block operators
`Q^x = ∑_a |a⟩ ⊗ Q^x_a`, `R^y = ∑_b |b⟩ ⊗ R^y_b` such that every `Q^x_a`, `R^y_b` has Pauli degree at
most `k`, `‖(Q^x)†Q^x − 𝟙‖₂ ≤ (2 + η)η` and `‖(R^y)†R^y − 𝟙‖₂ ≤ (2 + η)η` for all `x`, `y`, and the
approximate strategies `𝒬^x = ((Q^x_a)†Q^x_a)_a`, `ℛ^y = ((R^y_b)†R^y_b)_b` satisfy
`|Val_G(𝒬, ℛ) − Val_G(𝒜^{(u)}, ℬ^{(v)})| ≤ 15η`.

**Formalization Note** The constants are taken positive (`C, γ > 0`), as Theorem 3.1 and Figure 2
state for the same `γ`. `(Q^x)†Q^x = ∑_a (Q^x_a)†Q^x_a`; `‖·‖₂` is the normalized Schatten 2-norm.
The values are on `ψ^{⊗n}`; the approximate values use formula (22) (`val` on matrix families).
`log` is the natural logarithm. -/
theorem theorem_3_3 :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : MIPRE.Game X Y A B) (n : ℕ), 1 ≤ n →
      ∀ (w η : ℝ), 0 < w → 0 < η → η < 1 →
        2 ≤ max (Fintype.card A) (Fintype.card B) →
      ∀ (ψ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ), QAlgorithms.IsDensityMatrix ψ →
        HasMaxMixedMarginals ψ →
      ∀ (SA : X → MIPRE.POVM A (Fin n → Fin 2)) (SB : Y → MIPRE.POVM B (Fin n → Fin 2))
        (k : ℕ),
        (C * Real.log (2 * (max (Fintype.card A) (Fintype.card B) : ℝ)) / (w * η ^ 4)) ^
            (1 / γ) < (k : ℝ) →
        ∃ (u : X → ℝ) (v : Y → ℝ), (∀ x, w ≤ u x ∧ u x ≤ 2 * w) ∧ (∀ y, w ≤ v y ∧ v y ≤ 2 * w) ∧
        ∃ (Q : X → A → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
          (R : Y → B → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
          (∀ x a, HasPauliDegreeLE (Q x a) k) ∧ (∀ y b, HasPauliDegreeLE (R y b) k) ∧
          (∀ x, nnorm2 (∑ a, (Q x a)ᴴ * Q x a - 1) ≤ (2 + η) * η) ∧
          (∀ y, nnorm2 (∑ b, (R y b)ᴴ * R y b - 1) ≤ (2 + η) * η) ∧
          |val G (tensorPow ψ n) (fun x a => (Q x a)ᴴ * Q x a) (fun y b => (R y b)ᴴ * R y b) -
              val G (tensorPow ψ n) (fun x a => depolT (u x) n (povmMats SA x a))
                (fun y b => depolT (v y) n (povmMats SB y b))| ≤ 15 * η := by sorry

end UnitalMIP
