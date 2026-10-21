-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_proposition7
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.proposition7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:50:55.488321+00:00
-- url     : https://prove2.me/theorems/dd9b7108-3ae2-403b-a708-2bebde211d13
-- title:
--   Proposition 7: positive-map test for k-PEB
-- statement:
--   Let $H,H'$ be separable complex Hilbert spaces, $k\ge1$, and $\Phi:\mathcal T(H)\to\mathcal T(H')$ a quantum channel. Then
--
--   $$\Phi\in\mathcal P_k(H,H')\quad\Longleftrightarrow\quad\Lambda\circ\Phi\text{ is completely positive for every bounded $k$-positive }\Lambda:\mathcal T(H')\to\mathcal T(H').$$
--
--   The maps are complex-linear and need not preserve trace. Complete positivity tests every finite ancillary dimension; $\mathcal P_k$ uses all separable ancillas and all density inputs.
--
--   This characterizes partial entanglement breaking without imposing a bounded-rank Kraus decomposition.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 10, Proposition 7: positive-map test for k-PEB

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

/-- arXiv:1110.4363v3, PDF p.10, Proposition 7. The positive maps are bounded
endomorphisms of the output trace-class space; they need not preserve trace. -/
theorem proposition7 {I J : Type} [Countable I] [Countable J]
    (k : ℕ) (hk : 0 < k) (Phi : CanonicalChannel I J) :
    isPEB k Phi ↔ ∀ L : TraceMap J J, kPositive k L → cpComposition Phi L := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
