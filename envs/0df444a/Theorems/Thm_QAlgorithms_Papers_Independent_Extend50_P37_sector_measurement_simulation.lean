-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_sector_measurement_simulation
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.sector_measurement_simulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:28:36.955335+00:00
-- url     : https://prove2.me/theorems/f854cce1-585f-4dbd-a7a0-f74e947da343
-- title:
--   Corollary 10: symmetric-sector simulation by locally symmetric POVMs
-- statement:
--   Let $d,n\ge1$, $\mathcal A$ be a unital adjoint-closed algebra, and $M$ a normalized arbitrary-outcome POVM with global $G_{\mathcal A}$ symmetry. For each sign separately there is one normalized $\mathcal A^{\otimes n}$-valued POVM $\widetilde M_\pm=L_\pm(M)$ satisfying
--   $$\operatorname{tr}(\widetilde M_\pm(B)\rho)=\operatorname{tr}(M(B)\rho)$$
--   for every measurable $B$ and every density matrix $\rho=\Pi_\pm\rho\Pi_\pm$. The simulator is chosen before all such states, and the signs can require different simulators.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 14, Corollary 10: symmetric-sector simulation by locally symmetric POVMs

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF pp.14-15, Corollary 10: one simulator for all sector-supported states;
the two signs may have different simulators. -/
theorem sector_measurement_simulation [Nonempty I] {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) (s : Bool) (A : StarSubalgebra ℂ (Mat I))
    (M : Measurements.OperatorPOVM (Fin n → I) O)
    (hM : InAlgebra M.operator (Set.centralizer (collectiveImage n (unitaryCentralizer (A : Set (Mat I)))))) :
    ∃ N : Measurements.OperatorPOVM (Fin n → I) O,
      (∀ B, MeasurableSet B → N.operator B = promotion (A : Set (Mat I)) n s (M.operator B)) ∧
      InAlgebra N.operator (tensorAlg n (A : Set (Mat I))) ∧
      ∀ rho, IsDensityMatrix rho → permutationSector I n s * rho * permutationSector I n s = rho →
        ∀ B, MeasurableSet B → effectProb (M.operator B) rho = effectProb (N.operator B) rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
