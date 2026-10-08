-- Prove2me | Theorems.Thm_PerishableReturns_Suboptimal_theorem_1_and_2
-- name    : PerishableReturns.Suboptimal.theorem_1_and_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:52.770482+00:00
-- url     : https://prove2.me/theorems/180b8109-26ec-4824-b750-1c7808313a11
-- title:
--   Theorems 1–2: full-credit unlimited returns and no returns are system suboptimal
-- statement:
--   Let $c_3<c<c_1<p$ and let the retailer's and manufacturer's stockout goodwill costs $g,g_1$ be nonnegative. Demand is nonnegative, has finite mean, and has a continuous CDF. An integrated-company optimal order exists. Moreover, for every such order $Q$:
--
--   $$Q\notin\operatorname*{arg\,max}_{q\ge0}EP_R(q;c_1,c_1,1),\qquad
--     Q\notin\operatorname*{arg\,max}_{q\ge0}EP_R(q;c_1,c_2,0)\quad\text{for every }c_2.$$
--
--   Thus unlimited returns at full credit, and a policy allowing no returns, each make the retailer's optimal-order set disjoint from the integrated channel's optimal-order set. This gives the two suboptimality statements of Theorems 1 and 2 and the sentence combining them on p. 171.
--
--   **Formalization Note** A probability measure with nonnegative support and finite mean represents demand; atomlessness stands for the paper's density assumption and excludes deterministic demand, where Theorem 1 can fail. The existence clause prevents the disjointness claims from being vacuous. Orders are restricted to $Q\ge0$. At $R=0$, returns never occur and the retailer's profit is independent of $c_2$, so the conclusion quantifies over every credit, without an unused admissibility constraint. The goodwill-cost sign convention is needed for Theorem 2. Coordination means equality of optimal-order sets, while this theorem states the stronger disjointness asserted by the paper's wording.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), Theorems 1–2 and following sentence, p. 171; Appendix proofs, p. 175

import Mathlib
import Definitions.Def_PerishableReturns_Suboptimal_Model

namespace PerishableReturns.Suboptimal

open MeasureTheory

/-- Theorems 1 and 2, p. 171: full-credit unlimited returns and no returns fail to coordinate. -/
theorem theorem_1_and_2 (K : Costs) (c1 : ℝ) (hc : K.c < c1) (hp : c1 < K.p)
    (D : Measure ℝ) (hD : IsDemand D) [NullSingletonClass D] :
    (∃ Q : ℝ, IsOptimalOrder (EPT K D) Q) ∧
    (∀ Q : ℝ, IsOptimalOrder (EPT K D) Q →
      ¬ IsOptimalOrder (EPR K c1 c1 1 D) Q) ∧
    (∀ c2 Q : ℝ, IsOptimalOrder (EPT K D) Q →
      ¬ IsOptimalOrder (EPR K c1 c2 0 D) Q) := by sorry

end PerishableReturns.Suboptimal
