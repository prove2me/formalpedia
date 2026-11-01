-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_optimal_output_unique
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.optimal_output_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:51:20.062552+00:00
-- url     : https://prove2.me/theorems/89195fa3-6c08-41d1-a685-aa75f8973926
-- title:
--   §4: uniqueness of the average output of an optimal ensemble
-- statement:
--   Let $T$ be a trace-preserving completely positive channel from an arbitrary Hilbert input space to a finite output space. Let $\mathcal E=\{p_i,|x_i\rangle\}$ and $\mathcal F=\{q_j,|y_j\rangle\}$ be finite pure input ensembles: all vectors are unit vectors, all weights are nonnegative, and each family of weights sums to one. Suppose each attains the supremum $C(T)$ of the Holevo information $\chi=S(\sum_i p_i T(|x_i\rangle\langle x_i|))-\sum_i p_i S(T(|x_i\rangle\langle x_i|))$. Then
--   $$\sum_i p_iT(|x_i\rangle\langle x_i|)=\sum_jq_jT(|y_j\rangle\langle y_j|).$$
--   This identifies the average output independently of which attaining ensemble is chosen; it makes no assertion that an optimizer exists for every arbitrary input channel.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 6, §4: uniqueness of the average output of an optimal ensemble

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

/-- PDF pp.5--6: attaining ensembles have a unique average output. Input Hilbert
spaces are arbitrary; output dimension alone is finite. No attainment is postulated. -/
theorem optimal_output_unique {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {d : ℕ} (hd : 0 < d)
    (T : FiniteOutputDualChannel H d) (e f : SignalEnsemble H)
    (he : signalHolevo (pureOutput T) e = signalCapacity (pureOutput T))
    (hf : signalHolevo (pureOutput T) f = signalCapacity (pureOutput T)) :
    signalBarycenter (pureOutput T) e = signalBarycenter (pureOutput T) f := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
