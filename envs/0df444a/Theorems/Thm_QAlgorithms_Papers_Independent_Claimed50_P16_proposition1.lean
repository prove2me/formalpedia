-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_proposition1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.proposition1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:44:52.653091+00:00
-- url     : https://prove2.me/theorems/ed10522c-f0da-4f8a-a681-a2f4cd8d71eb
-- title:
--   Proposition 1 (A–C)
-- statement:
--   Let $H,K$ be separable complex Hilbert spaces. Density states carry the trace norm. For a pure state $\sigma$, let $\mathrm{SR}(\sigma)$ be its Schmidt rank, with infinity allowed. Let $\mathcal P_\rho$ be the Borel probability measures on pure states with barycenter $\rho$, and put
--
--   $$\mathrm{SN}(\rho)=\inf_{\mu\in\mathcal P_\rho}\operatorname*{ess\,sup}_{\mu}\mathrm{SR}.$$
--
--   This function is lower semicontinuous, and every infimum is attained at an extreme point of its fixed-barycenter fiber. For every positive integer $k$, the class $S_k=\{\rho:\mathrm{SN}(\rho)\le k\}$ is closed and convex and equals the trace-norm closed convex hull of the pure states of Schmidt rank at most $k$. If $\rho$ has finite operator rank, its Schmidt number equals the infimum, over countable pure ensembles representing $\rho$, of the supremum of their positive-weight components' Schmidt ranks. This equality also includes the value infinity.
--
--   These assertions identify the continuous roof with the mixed Schmidt classes without imposing countable decomposability.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 6, Proposition 1 (A–C)

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

/-- arXiv:1110.4363v3, PDF p.6, Proposition 1 A–C (definition (2) on p.5).
All clauses are retained, including equality of the two roofs for finite operator
rank with possibly infinite Schmidt number. Extreme measures are in a fixed fiber. -/
theorem proposition1 {I J : Type} [Countable I] [Countable J] :
    (∀ c : ℝ≥0∞, IsClosed {rho : State (I × J) | continuousSchmidtNumber rho ≤ c}) ∧
    (∀ rho : State (I × J), ∃ mu : Measure (pureStates (I × J)),
      extremeFiber rho mu ∧
        essSup (fun sigma => schmidtRank (pureStateFromRange sigma)) mu =
          continuousSchmidtNumber rho) ∧
    (∀ k : ℕ, 0 < k → IsClosed (schmidtClass I J k) ∧ stateConvex (schmidtClass I J k) ∧
      schmidtClass I J k = stateHull (pureClass I J k)) ∧
    (∀ rho : State (I × J), (∃ k, arrayRankLE k rho.coefficients) →
      continuousSchmidtNumber rho = discreteSchmidtNumber rho) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
