-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_proposition5
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.proposition5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:48:06.866298+00:00
-- url     : https://prove2.me/theorems/8aa3b7ff-0964-4c71-8bed-b3ad10c4119f
-- title:
--   Proposition 5: optimal edge decomposition
-- statement:
--   Let $H,K$ be infinite-dimensional separable complex Hilbert spaces, $k\ge2$, and $\rho\in S_k$. There exist $p\in[0,1]$, $\eta\in S_{k-1}$, and a density state $\delta$ with $\mathrm{SN}(\delta)\ge k$ such that
--
--   $$\rho=(1-p)\eta+p\delta,\qquad\delta-\lambda\sigma\not\ge0\quad(\lambda>0,\ \sigma\in S_{k-1}).$$
--
--   Among all such decompositions there is one whose weight $p$ is minimal. The test uses every mixed state in $S_{k-1}$. The endpoints $p=0,1$ are included.
--
--   This gives an attained optimal edge decomposition. The restriction $k\ge2$ corrects the impossible requirement $\eta\in S_0=\varnothing$ at $k=1$.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 8, Proposition 5: optimal edge decomposition

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

/-- arXiv:1110.4363v3, PDF pp.8–9, Proposition 5. Printed: no restriction k>=2.
Changed: k>=2, because its eta in S_0 is impossible at k=1 (footnote 3).
The optimal weight is attained; endpoints do not divide a zero remainder. -/
theorem proposition5 {I J : Type} [Countable I] [Countable J] [Infinite I] [Infinite J]
    (k : ℕ) (hk : 2 ≤ k) (rho : State (I × J)) (hrho : rho ∈ schmidtClass I J k) :
    ∃ (p : ℝ) (eta delta : State (I × J)), edgeDecomposition k rho eta delta p ∧
      ∀ (q : ℝ) (eta2 delta2 : State (I × J)), edgeDecomposition k rho eta2 delta2 q → p ≤ q := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
