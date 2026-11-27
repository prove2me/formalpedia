-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_9_2_2
-- name    : WildeQIT.Compression.Supplement.theorem_9_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:11:59.038892+00:00
-- url     : https://prove2.me/theorems/283332b1-914d-4abc-b60a-fe3c86d8bad9
-- title:
--   Theorem 9.2.2 (Measurement Achieves Fidelity): $F(\rho,\sigma)=\min_{\{\Lambda_x\}}\big[\sum_x\sqrt{\operatorname{Tr}\{\Lambda_x\rho\}\operatorname{Tr}\{\Lambda_x\sigma\}}\big]^2$
-- statement:
--   Let $\rho,\sigma\in\mathcal D(\mathcal H)$ be density operators and let $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ be their fidelity. Then the fidelity is the minimum of the classical fidelity of the outcome distributions over all measurements:
--
--   $$
--   F(\rho,\sigma)=\min_{\{\Lambda_x\}}\Big[\sum_{x\in\mathcal X}\sqrt{\operatorname{Tr}\{\Lambda_x\rho\}\operatorname{Tr}\{\Lambda_x\sigma\}}\Big]^2,
--   $$
--
--   where the minimum is over all POVMs $\{\Lambda_x\}_{x\in\mathcal X}$ with a finite outcome set. That is:
--
--   1. for every POVM, $F(\rho,\sigma)\le\big[\sum_x\sqrt{\operatorname{Tr}\{\Lambda_x\rho\}\operatorname{Tr}\{\Lambda_x\sigma\}}\big]^2$;
--   2. some POVM attains equality.
--
--   The theorem gives an operational meaning to the fidelity: it is the smallest classical fidelity of the measurement statistics.
--
--   **Formalization Note** The fidelity is the published squared fidelity; POVMs are the published `WildeQIT.QMemory.IsPOVM`.
--
--   Differences from the source:
--   - encoding: a minimum over all POVMs → two clauses: the bound for every POVM with any finite outcome type, and equality for some POVM with outcome set Fin k; reason: "min" asserts both that the value is a lower bound and that it is attained; every finite outcome set is in bijection with some Fin k
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 9.2.2, p. 272, eqs. (9.150)–(9.151)

import Mathlib
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QMemory_IsPOVM

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 9.2.2, p. 272.
-/

namespace WildeQIT.Compression.Supplement

/-- **Theorem 9.2.2 (Measurement Achieves Fidelity)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 272, (9.151)): for
`ρ, σ ∈ D(H)`, `F(ρ, σ) = min_{Λ_x} [∑_{x∈X} √(Tr{Λ_x ρ} Tr{Λ_x σ})]²`, "where the minimization
is with respect to all POVMs".

Formalization Note: the minimum is stated as its two clauses: (1) the bound (9.150) for every
POVM with any finite outcome set `X`, and (2) attainment by some POVM, with a finite outcome set
`Fin k`. `F` is the published squared fidelity `‖√ρ√σ‖₁²`; POVMs are the published
`WildeQIT.QMemory.IsPOVM`; `Tr{Λ_x ρ}` is real for these operators and its real part is taken. -/
theorem theorem_9_2_2 {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    (∀ (X : Type) [Fintype X] (Λ : X → Matrix n n ℂ), WildeQIT.QMemory.IsPOVM Λ →
      fidelity ρ σ ≤ (∑ x, Real.sqrt ((Λ x * ρ).trace.re * (Λ x * σ).trace.re)) ^ 2) ∧
    ∃ (k : ℕ) (Λ : Fin k → Matrix n n ℂ), WildeQIT.QMemory.IsPOVM Λ ∧
      fidelity ρ σ = (∑ x, Real.sqrt ((Λ x * ρ).trace.re * (Λ x * σ).trace.re)) ^ 2 := by sorry

end WildeQIT.Compression.Supplement
