-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P38_strongSubadditivity
-- name    : QAlgorithms.Papers.Independent.Gap48.P38.strongSubadditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:09:32.446285+00:00
-- url     : https://prove2.me/theorems/62273855-16d1-4862-92f9-394ca8a7465f
-- title:
--   §IV, unnumbered: operational strong subadditivity
-- statement:
--   Let $|\psi\rangle^{ABCD}$ be an arbitrary unit vector on nonempty finite complex registers, permitting trivial one-dimensional subsystems. Compute all marginals by partial trace and all entropies in bits. Then
--
--   $$I(C;D\mid B)=H(CB)+H(DB)-H(B)-H(CDB)\ge0.$$
--
--   This is the strong-subadditivity conclusion established operationally in Section IV, not merely an intermediate finite-block communication bound.
-- source:
--   Optimal quantum source coding with quantum information at the encoder and decoder, arXiv:0706.2907v2, PDF p. 8, §IV, unnumbered: operational strong subadditivity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap48.P38

/-- Section IV's main result, PDF pp.8--9: strong subadditivity for every
normalized pure ABCD, with actual marginals and finite entropy in bits. -/
theorem strongSubadditivity
    (I : Fin 4 → Type) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (psi : EuclideanSpace ℂ (∀ i, I i)) (hpsi : ‖psi‖ = 1) :
    0 ≤ registerCMI I (pureDensity psi) {2} {3} {1} := by sorry

end QAlgorithms.Papers.Independent.Gap48.P38

end
