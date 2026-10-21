-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_proposition9A
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.proposition9A
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:53:14.992715+00:00
-- url     : https://prove2.me/theorems/2b362150-1b84-4699-a25d-4da1405779bc
-- title:
--   Proposition 9A: bounded-rank Kraus representation is sufficient
-- statement:
--   Let $H,H'$ be separable complex Hilbert spaces, $k\ge1$, and $\Phi:\mathcal T(H)\to\mathcal T(H')$ a channel with a countable Kraus representation
--
--   $$\Phi(X)=\sum_i V_iXV_i^*,\qquad\operatorname{rank}V_i\le k\quad\text{for every }i.$$
--
--   The operator sum $\sum_iV_i^*V_i=I$ converges strongly, and the displayed series converges in trace norm for every trace-class $X$. Then $\Phi$ is $k$-partially entanglement breaking. Finite representations are included by zero padding.
--
--   This is a sufficient condition; no infinite-dimensional converse is asserted.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 12, Proposition 9A: bounded-rank Kraus representation is sufficient

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

/-- arXiv:1110.4363v3, PDF p.12, Proposition 9A. Sufficient bounded-rank Kraus
condition only; the converse fails. The rank bounds concern the supplied representation. -/
theorem proposition9A {I J : Type} [Countable I] [Countable J]
    (k : ℕ) (hk : 0 < k) (Phi : CanonicalChannel I J) (V : ℕ → BoundedOp I J)
    (hrep : krausRepresentation Phi V) (hrank : ∀ i, arrayRankLE k (opCoeff (V i))) :
    isPEB k Phi := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
