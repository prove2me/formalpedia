-- Prove2me | Theorems.Thm_SupplyChainCarbon_Necessity_first_best_marginal_condition
-- name    : SupplyChainCarbon.Necessity.first_best_marginal_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:36:35.267181+00:00
-- url     : https://prove2.me/theorems/339e84da-1f0b-419e-b307-c4a3d5137389
-- title:
--   Lemma 7 — first-best marginal condition (necessity and sufficiency)
-- statement:
--   Consider arbitrary positive finite firm, process and action counts and continuous efforts $e\in E=\prod_n[0,A]^{m_n}$, $A>0$. Costs and footprints satisfy all standing assumptions in §§3.1–3.2: differentiable convex strictly increasing own-effort costs, constant operating revenues, and differentiable convex nonincreasing nonnegative process footprints on their domains. Let $p=p_S>0$ and let $e^*$ be the unique global social maximizer, interior in every effort coordinate. Compute the binary influence matrix $b(e^*)$ from the footprint derivatives there and require every row and column to be nonempty. Let $h$ be any differentiable payment rule of (5), including differentiable allocations and balanced internal transfers, and put $f^*=f(e^*)$.
--
--   If $e^*$ is a Nash equilibrium against every feasible unilateral effort-block deviation, then for every firm $n$ and action $j$,
--
--   $$\sum_i \frac{\partial f_i}{\partial e_{n,j}}(e^*)\big(D_i h_n(f^*)-p_S\big)=\sum_i \frac{\partial f_i}{\partial e_{n,j}}(e^*)\big(D_i h_n(f^*)-p_S b_{n,i}(e^*)\big)=0.$$
--
--   Conversely, if each $h_n$ is componentwise nondecreasing and convex on the nonnegative footprint orthant, this entire condition implies that $e^*$ is a Nash equilibrium. The necessary clause assumes neither monotonicity nor convexity of payments. The sufficient clause makes no claim about participation or uniqueness of the decentralized equilibrium.
--
--   This complete lemma supplies the marginal incentive condition supporting the impossibility result. Both equalities and both implications are retained.
--
--   Differences from the source:
--   - encoding: one-based finite firm, process and action indices with continuous real effort blocks → zero-based Fin indices with arbitrary positive finite counts and dependent products of real blocks; reason: a bijective reindexing preserves every object and feasible effort
--   - encoding: differentiable functions on the effort boxes and nonnegative footprint domain → DifferentiableOn and fderivWithin on those domains, with arbitrary unused ambient values; reason: domain derivatives preserve the source instances without requiring an exterior differentiable extension
--   - encoding: own-effort profit written as a constant minus convex strictly increasing abatement cost → profit is computed from the constant and cost fields of Technology; reason: this directly implements the stated profit decomposition and implies the stated profit regularity
--   - reading: the evaluation point in the definition of the influence matrix is suppressed → incidence is computed from effort derivatives at the designated eStar; reason: Appendix A.1 uses strict influence derivatives at the implementing first best; globally invariant incidence is not required
--   - reading: achieving first-best and sufficiency of the marginal equation, with participation stated separately → both clauses characterize Nash incentives, with no participation assertion in the sufficient clause; reason: equations in derivatives do not imply inequalities for arbitrary reservation profits
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, Appendix A, Lemma 7, p. 24, Eq. (14)

import Definitions.Def_SupplyChainCarbon_Necessity_Marginals

namespace SupplyChainCarbon.Necessity

/-- Caro et al., December 21, 2012, Lemma 7, p. 24: all of (14), both directions. -/
theorem first_best_marginal_condition
    (N I : ℕ) (m : Fin N → ℕ) (C : Technology N I m)
    (pS : ℝ) (hpS : 0 < pS) (R : PaymentRule N I pS)
    (eStar : Effort N m)
    (hfirst : CarbonDoubleCount.Planner.IsFirstBest C.bound (profit C) C.footprint pS eStar)
    (hunique : ∀ e ∈ effortBox m C.bound,
      CarbonDoubleCount.Planner.IsFirstBest C.bound (profit C) C.footprint pS e → e = eStar)
    (hinterior : ∀ n j, 0 < eStar n j ∧ eStar n j < C.bound)
    (hrelevant : relevantIncidence C eStar)
    : (isNash C R eStar → marginalCondition C R eStar) ∧
      ((∀ n, MonotoneOn (R.payment n) (footprintOrthant I)) →
       (∀ n, ConvexOn ℝ (footprintOrthant I) (R.payment n)) →
       marginalCondition C R eStar → isNash C R eStar) := by sorry

end SupplyChainCarbon.Necessity
