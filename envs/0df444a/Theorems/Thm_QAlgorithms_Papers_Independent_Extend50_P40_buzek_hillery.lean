-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_buzek_hillery
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.buzek_hillery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:00:04.328697+00:00
-- url     : https://prove2.me/theorems/681a134b-bf05-4155-a7c8-11e344352db7
-- title:
--   §II.A.2 Eqs.(12)–(14): Buzek–Hillery cloner
-- statement:
--   Let $V$ be the two-column Buzek–Hillery map (12), with the second normalized Bell coefficient corrected to $\sqrt{1/3}$ and the printed minus on input $|1\rangle$ retained. It is an isometry, and discarding its machine gives a CPTP channel. For every normalized input $\psi$,
--
--   $$
--   \rho_A=\rho_B=\tfrac23|\psi\rangle\langle\psi|+\tfrac16 I,\qquad F_A=F_B=\tfrac56.
--   $$
--
--   The column construction fixes the machine before the input. The source coefficient correction is documented for independent moderation.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 8, §II.A.2 Eqs.(12)–(14): Buzek–Hillery cloner

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- II.A.2, PDF p.8 Eqs.(12)–(14): corrected normalized BH construction and its marginals.
Printed sqrt(1/6) on the second normalized Bell term is changed to sqrt(1/3),
forced by (13). This correction requires independent moderation. -/
theorem buzek_hillery :
    bhMatrixᴴ * bhMatrix = 1 ∧ IsChannel (cloneChannel bhMatrix) ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 → ‖bhOutput psi‖ = 1 ∧
      cloneMarginalA (bhOutput psi) = depol (2 / 3) (pureDensity psi) ∧
      cloneMarginalB (bhOutput psi) = depol (2 / 3) (pureDensity psi) ∧
      pureFidelity psi (cloneMarginalA (bhOutput psi)) = 5 / 6 ∧
      pureFidelity psi (cloneMarginalB (bhOutput psi)) = 5 / 6) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
