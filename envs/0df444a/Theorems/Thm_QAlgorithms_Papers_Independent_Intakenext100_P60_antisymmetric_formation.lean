-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_antisymmetric_formation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.antisymmetric_formation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:59:36.181833+00:00
-- url     : https://prove2.me/theorems/7488c25e-11f4-483e-8f37-9e5aedc1b509
-- title:
--   Example 8: antisymmetric qutrit support has constant formation one
-- statement:
--   Let $A\subset\mathbb C^3\otimes\mathbb C^3$ be the antisymmetric subspace spanned by
--   $$\frac{|12\rangle-|21\rangle}{\sqrt2},\quad\frac{|20\rangle-|02\rangle}{\sqrt2},\quad\frac{|01\rangle-|10\rangle}{\sqrt2}.$$
--   For every positive trace-one matrix $\rho$ supported on $A$,
--   $$E_f(\rho)=1.$$
--   Formation is measured across the two qutrits, in bits, by the normalized pure-state convex roof. This claim concerns formation for every supported state; the subsequent cited cost result concerns the particular maximally mixed antisymmetric state.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 14, Example 8: antisymmetric qutrit support has constant formation one

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P60

namespace QAlgorithms.Papers.Independent.Intakenext100.P60

open scoped Matrix ComplexConjugate ComplexOrder TensorProduct

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix, normalized ensemble, convex roof, grouped copies and LOCC.

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble pureAverage formation)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open QAlgorithms.Papers.Independent.Gap48.P32 (twoWayDistillable)

/-- PDF pp.13--14, Example 8: formation, without a cost claim for arbitrary states.
The later tensor-power cost result for the maximally mixed state is cited background. -/
theorem antisymmetric_formation (rho : Op (Fin 3 × Fin 3)) (hrho : IsDensityMatrix rho)
    (hsupport : HasRangeIn (dilationSpace antisymmetricDilation) rho) :
    formation rho = 1 := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
