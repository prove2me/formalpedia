-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_positivityDetectsDistillability
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.positivityDetectsDistillability
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:09:39.201683+00:00
-- url     : https://prove2.me/theorems/695efe13-8fc0-49d3-9973-31587fc0f03f
-- title:
--   Positivity detects PPT distillability
-- statement:
--   Let $\rho$ be any normalized bipartite state on nonzero finite-dimensional complex spaces. Let $E_W$ be the logarithm of SDP (7), and define $E_\Gamma$ by the supremum of rates whose Eq. (3) distillation fidelity tends to one. Then
--
--   $$E_W(\rho)>0\quad\Longleftrightarrow\quad E_\Gamma(\rho)>0.$$
--
--   Moreover, $T_B(\rho)\ge0$ implies $E_W(\rho)=0$. Thus positivity of this SDP measure detects positive-rate PPT distillability, including rank-deficient states.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 3, Theorem 2: positivity detects PPT distillability

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

/-- Theorem 2 and its PPT-zero case, PDF p.3. The NPPT characterization
is a conclusion of the proof, not an extra hypothesis. -/
theorem positivityDetectsDistillability [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    (0 < entanglementW rho ↔ 0 < entanglementGamma rho) ∧
    ((partialTranspose rho).PosSemidef → entanglementW rho = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
