-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_optimal_output_product
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.optimal_output_product
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:52:13.56599+00:00
-- url     : https://prove2.me/theorems/2b93fcdc-c8ad-4b59-90d1-3031349bb3af
-- title:
--   §4, equation (9): additivity implies a product optimal output
-- statement:
--   Let $T$ and $T'$ be trace-preserving completely positive channels with arbitrary Hilbert input spaces and finite positive-dimensional output spaces. Suppose
--   $$C(T\otimes T')=C(T)+C(T').$$
--   For any normalized finite pure ensembles attaining these three Holevo suprema, denote their average output density matrices by $\omega$, $\omega'$ and $\Omega$, respectively. The joint channel is the actual tensor channel on the completed Hilbert tensor product, allowing entangled inputs of arbitrary Schmidt rank. Then
--   $$\Omega=\omega\otimes\omega'.$$
--   This is a consequence of the stated additivity premise, with attainment assumed only for the three ensembles being compared.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 6, §4, equation (9): additivity implies a product optimal output

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

/-- PDF p.6, (9): conditional on capacity additivity, any three attaining ensembles
have the stated product output. The joint channel and all its entangled inputs are
constructed using the completed Hilbert tensor product. -/
theorem optimal_output_product {H K : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (T : FiniteOutputDualChannel H d) (S : FiniteOutputDualChannel K e)
    (hadd : signalCapacity (tensorDualOutput T S) =
      signalCapacity (pureOutput T) + signalCapacity (pureOutput S))
    (a : SignalEnsemble H) (b : SignalEnsemble K)
    (c : SignalEnsemble (UniformSpace.Completion (H ⊗[ℂ] K)))
    (ha : signalHolevo (pureOutput T) a = signalCapacity (pureOutput T))
    (hb : signalHolevo (pureOutput S) b = signalCapacity (pureOutput S))
    (hc : signalHolevo (tensorDualOutput T S) c = signalCapacity (tensorDualOutput T S)) :
    signalBarycenter (tensorDualOutput T S) c =
      Matrix.kronecker (signalBarycenter (pureOutput T) a) (signalBarycenter (pureOutput S) b) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
