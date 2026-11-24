-- Prove2me | Theorems.Thm_TwoSidedMatching_Statics_Supplement_theorem_1_counterexample
-- name    : TwoSidedMatching.Statics.Supplement.theorem_1_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:05:18.238166+00:00
-- url     : https://prove2.me/theorems/4009f54f-0dcb-40d2-aeb1-85a22c57e4b0
-- title:
--   Theorem 1 (corrected: counterexample at zero volume) — threshold acceptance can be worse than rejection
-- statement:
--   Consider independent rate-one Poisson buyers and sellers over $[0,1]$, with buyer values uniform on $[0,1]$ and seller costs uniform on $[1,2]$. Both virtual functions are increasing and the densities are continuous. Equations (1)–(2) give $\mu^*=0$ and $p^*=w^*=1$. All myopic opponent request streams are empty almost surely.
--
--   For a tagged buyer with $v=1$ or seller with $c=1$, arrival time $t=1/2$ and waiting cost $b=h=2$, the expected utilities, each integrable, satisfy
--
--   $$\mathbb E[U^d_{\rm accept}]=\mathbb E[U^s_{\rm accept}]=-1<0=\mathbb E[U^d_{\rm reject}]=\mathbb E[U^s_{\rm reject}].$$
--
--   Both actions stop at arrival; acceptance is precisely the printed threshold-tie action. Rejection is a strictly better admissible alternative. This refutes both universal best-response claims on the printed domain, rather than proposing a weaker strategic-myopia result. **Formalization Note** The tagged types are in their closed supports, the arrival time is interior, and utilities are computed under the actual primitive probability measure. Payments are zero when unmatched; the argument does not evaluate a compensation ratio with a zero match probability.
--
--   Differences from the source:
--   - correction: Theorem 1 asserts immediate threshold acceptance is a best response for every type, including ties and zero-volume markets → an explicit touching-support counterexample has expected utility -1 from acceptance and 0 from rejection, on both sides; reason: no opponent ever requests almost surely, so an accepted tagged request waits to T without any payment; no finite price or zero-probability convention compensates an unmatched request
--   - encoding: conditional utilities at each tagged type → Palm insertion at interior arrival time 1/2 under the published opponent law, with both initial signals deterministic almost surely; reason: the conditional comparison reduces to ordinary expectation, and the two constant actions are admissible under either source information structure
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), main text p. 19, Theorem 1; pp. 9–13, utility and departure rules; Supplemental Note pp. 9–10, proof of Theorem 1

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Supplement_Deviation

open MeasureTheory

namespace TwoSidedMatching.Statics.Supplement

/-- Counterexample to both threshold-tie assertions in Theorem 1 on its full printed domain.
The tagged types v=c=1 belong to their closed supports. Both constant actions are adapted.
No assumption about a general equilibrium or conditional compensation is used. -/
theorem theorem_1_counterexample :
    touchingMarket.Regular ∧ touchingMarket.loS = touchingMarket.hiB ∧
    ContinuousOn touchingMarket.fB (Set.Icc touchingMarket.loB touchingMarket.hiB) ∧
    ContinuousOn touchingMarket.fS (Set.Icc touchingMarket.loS touchingMarket.hiS) ∧
    TwoSidedMatching.Guarantee.muStar touchingMarket 1 1 1 = 0 ∧
    TwoSidedMatching.Guarantee.pStar touchingMarket 1 1 1 = 1 ∧
    TwoSidedMatching.Guarantee.wStar touchingMarket 1 1 1 = 1 ∧
    IsProbabilityMeasure (TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) ∧
    (∀ᵐ ω ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1,
      TwoSidedMatching.Guarantee.reqB touchingMarket 1 1 1 ω = ∅ ∧
      TwoSidedMatching.Guarantee.reqS touchingMarket 1 1 1 ω = ∅) ∧
    (∀ a : Bool,
      Integrable (buyerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) a))
        (TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) ∧
      Integrable (sellerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) a))
        (TwoSidedMatching.Guarantee.P touchingMarket 1 1 1)) ∧
    (∫ ω, buyerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) true) ω
      ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) = -1 ∧
    (∫ ω, buyerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) false) ω
      ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) = 0 ∧
    (∫ ω, sellerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) true) ω
      ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) = -1 ∧
    (∫ ω, sellerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) false) ω
      ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) = 0 := by sorry

end TwoSidedMatching.Statics.Supplement
