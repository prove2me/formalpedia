-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_proposition3
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.proposition3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:46:26.067237+00:00
-- url     : https://prove2.me/theorems/95f84bba-e157-444c-a40e-e62c70df7d72
-- title:
--   Proposition 3 (A–C)
-- statement:
--   Let $H,K$ be infinite-dimensional separable complex Hilbert spaces and $k\ge1$. Write $S_k=\{\rho:\mathrm{SN}(\rho)\le k\}$, set $S_0=\varnothing$, and let $S_k^p$ consist of its pure states. Every $\rho\in S_k$ is the barycenter of a Borel probability measure on $S_k^p$ that is extreme in the fiber with barycenter $\rho$.
--
--   There exists $\rho\in S_k\setminus S_{k-1}$ such that
--
--   $$\rho-\lambda\sigma\not\ge0\qquad(\lambda>0,\ \sigma\text{ pure},\ \mathrm{SR}(\sigma)<\infty).$$
--
--   For every such $\rho$, every positive-weight component in every countable pure decomposition has infinite Schmidt rank. Every pure state in $S_k\setminus S_{k-1}$ is a trace-norm limit of states in this same stratum satisfying the displayed property.
--
--   This distinguishes the continuous Schmidt classes from the ranks appearing in countable decompositions.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 7, Proposition 3 (A–C)

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

/-- arXiv:1110.4363v3, PDF pp.7–8, Proposition 3 A–C.
Printed A: extreme in all P(S_k^p). Changed: extreme in its fixed-barycenter fiber,
as Proposition 1A and the proof require; otherwise mixed barycenters are impossible.
Only positive-weight ensemble terms have the rank asserted in B. S_0 is empty. -/
theorem proposition3 {I J : Type} [Countable I] [Countable J] [Infinite I] [Infinite J]
    (k : ℕ) (hk : 0 < k) :
    (∀ rho ∈ schmidtClass I J k, ∃ mu : Measure (pureClass I J k), extremeFiber rho mu) ∧
    (∃ rho ∈ schmidtClass I J k \ schmidtClass I J (k - 1), noFinitePurePart rho) ∧
    (∀ rho ∈ schmidtClass I J k \ schmidtClass I J (k - 1),
      noFinitePurePart rho → allEnsembleRanksInfinite rho) ∧
    (∀ rho ∈ pureClass I J k \ schmidtClass I J (k - 1),
      ∃ r : ℕ → State (I × J),
        (∀ n, r n ∈ schmidtClass I J k \ schmidtClass I J (k - 1) ∧ noFinitePurePart (r n)) ∧
        Tendsto r atTop (nhds rho)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
