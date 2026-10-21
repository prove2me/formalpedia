-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_proposition4
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.proposition4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:47:08.340901+00:00
-- url     : https://prove2.me/theorems/c98b9723-6681-4d01-82e9-fc7b723ec006
-- title:
--   Proposition 4: k-positive-map characterization
-- statement:
--   Let $H,K$ be infinite-dimensional separable complex Hilbert spaces, $k\ge1$, and $\rho$ a density operator on $H\otimes K$. Then
--
--   $$\rho\in S_k\quad\Longleftrightarrow\quad (\Lambda\otimes\operatorname{Id}_K)(\rho)\ge0\ \text{for every bounded $k$-positive complex-linear }\Lambda:\mathcal T(H)\to\mathcal T(H).$$
--
--   Here $\mathcal T(H)$ is the trace-class Banach space and $S_k$ is the continuous Schmidt class. Positivity of the slice-defined infinite amplification means positivity of every finite ancillary corner. It does not assert a trace-class infinite amplification for an arbitrary positive map.
--
--   This is the positive-map characterization in the source's infinite-dimensional domain.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 8, Proposition 4: k-positive-map characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P16

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize traceClosure rankOne
   productCoeff IsBarycenter IsTraceClosed tensorApply IsSeparable)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceSecond traceFirst)

open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)

/-- arXiv:1110.4363v3, PDF p.8, Proposition 4. Endomorphisms of the full trace-class
space are retained. Infinite amplification positivity tests all finite corners;
no globally trace-class infinite amplification is assumed for a positive map. -/
theorem proposition4 {I J : Type} [Countable I] [Countable J] [Infinite I] [Infinite J]
    (k : ℕ) (hk : 0 < k) (rho : State (I × J)) :
    rho ∈ schmidtClass I J k ↔
      ∀ L : TraceMap I I, kPositive k L → positiveArray (tensorApply L.apply rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
