-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_comparisonWithNegativity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.comparisonWithNegativity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:12:20.030978+00:00
-- url     : https://prove2.me/theorems/5a2b8c70-7a56-445c-a445-80be6f7b7109
-- title:
--   Comparison with logarithmic negativity and equality criterion
-- statement:
--   Let $\rho$ be any normalized finite-dimensional bipartite state, and write $E_N(\rho)=\log_2\|T_B(\rho)\|_1$. With $W$ defined by SDP (7) and $E_W=\log_2W$, one has
--
--   $$E_W(\rho)\le E_N(\rho).$$
--
--   There exists a normalized finite-dimensional state for which the inequality is strict. For each $\rho$, equality holds exactly when there is a Hermitian matrix $R$ satisfying
--
--   $$\|R\|_\infty\le1,\quad \operatorname{Re}\operatorname{Tr}(T_B(\rho)R)=\|T_B(\rho)\|_1,\quad T_B(R)\ge0.$$
--
--   Thus equality is characterized by a partial-transpose-positive optimizer of (10). Positivity of $R$ itself is not required.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 4, Theorem 4: comparison with logarithmic negativity and equality criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P83

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P83

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

variable {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Theorem 4, PDF p.4: universal comparison, possible strict improvement,
and equality exactly when (10) has a Hermitian optimizer whose partial transpose
is positive. Positivity of the optimizer itself is not required. -/
theorem comparisonWithNegativity [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    entanglementW rho ≤ entanglementN rho ∧
    (∃ a b : ℕ, ∃ sigma : Matrix (Fin (a+1) × Fin (b+1)) (Fin (a+1) × Fin (b+1)) ℂ,
      IsDensityMatrix sigma ∧ entanglementW sigma < entanglementN sigma) ∧
    (entanglementW rho = entanglementN rho ↔
      ∃ R : Matrix (A × B) (A × B) ℂ,
        R.IsHermitian ∧ complexSpectralNorm R ≤ 1 ∧
        effectProb (partialTranspose rho) R = traceNorm (partialTranspose rho) ∧
        (partialTranspose R).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
