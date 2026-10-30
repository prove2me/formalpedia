-- Prove2me | Theorems.Thm_SupplyChainCarbon_Necessity_double_counting_necessary
-- name    : SupplyChainCarbon.Necessity.double_counting_necessary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:37:32.983058+00:00
-- url     : https://prove2.me/theorems/ef1802cb-7ce8-4a23-b2da-c25e40c4a306
-- title:
--   Proposition 2 — double-counting is necessary for first-best effort
-- statement:
--   Consider arbitrary positive finite firm, process and action counts and continuous efforts in $E=\prod_n[0,A]^{m_n}$, $A>0$. Each firm has differentiable convex strictly increasing own-effort abatement costs and constant operating revenues; its profit is the constant minus its cost. Each process footprint is differentiable, convex, componentwise nonincreasing and nonnegative on $E$. At the exact price $p=p_S>0$, let $e^*$ be the unique global social maximizer and be interior in every effort coordinate. The influence matrix computed at $e^*$ has no empty row or column and includes a process influenced by at least two distinct firms.
--
--   Let $h$ be any differentiable, componentwise nondecreasing carbon-based payment rule of (5), with differentiable footprint allocations and balanced internal transfers on $F=\mathbb R_{\ge0}^I$. For arbitrary given reservation profits $\pi_n$, suppose $e^*$ satisfies participation and is a Nash equilibrium for all feasible whole-block unilateral deviations. Then
--
--   $$\exists i\in\mathcal I,\qquad\sum_{n\in\mathcal N}D_i h_n(f(e^*))>p_S.$$
--
--   The derivative is with respect to a footprint coordinate. Some process must be overcharged at the first-best footprint; the claim does not specify which joint process, nor require excess for every joint process. Total payments may be nonlinear and nonconvex. No footprint balance, upper bound on marginal payments, or first-order incentive condition is assumed.
--
--   This is a restriction on incentives rather than emissions inventories. Balanced internal transfers do not permit first-best implementation while keeping every aggregate marginal charge at or below the social carbon price.
--
--   Differences from the source:
--   - encoding: one-based finite firm, process and action indices with continuous real effort blocks → zero-based Fin indices with arbitrary positive finite counts and dependent products of real blocks; reason: a bijective reindexing preserves every object and feasible effort
--   - encoding: differentiable functions on the effort boxes and nonnegative footprint domain → DifferentiableOn and fderivWithin on those domains, with arbitrary unused ambient values; reason: domain derivatives preserve the source instances without requiring an exterior differentiable extension
--   - encoding: own-effort profit written as a constant minus convex strictly increasing abatement cost → profit is computed from the constant and cost fields of Technology; reason: this directly implements the stated profit decomposition and implies the stated profit regularity
--   - reading: the evaluation point in the definition of the influence matrix is suppressed → incidence is computed from effort derivatives at the designated eStar; reason: Appendix A.1 uses strict influence derivatives at the implementing first best; globally invariant incidence is not required
--   - encoding: the game is conditional on participation for given reservation profits → participation at eStar is a separate hypothesis for an arbitrary reservation vector; reason: the source participation convention is retained independently of the Nash best-response predicate
--   - encoding: double-counting is necessary, with derivative arguments suppressed in Appendix A.1 → some process has aggregate marginal payment strictly above pS at f(eStar); reason: this makes explicit the evaluation point used in the source proof without asserting excess for every joint process
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, Proposition 2, p. 12; Appendix A.1, pp. 24–25

import Definitions.Def_SupplyChainCarbon_Necessity_Marginals

namespace SupplyChainCarbon.Necessity

/-- Proposition 2, p. 12; influence is evaluated at eStar, as in Appendix A.1. -/
theorem double_counting_necessary
    (N I : ℕ) (m : Fin N → ℕ) (C : Technology N I m)
    (pS : ℝ) (hpS : 0 < pS) (R : PaymentRule N I pS)
    (eStar : Effort N m)
    (hfirst : CarbonDoubleCount.Planner.IsFirstBest C.bound (profit C) C.footprint pS eStar)
    (hunique : ∀ e ∈ effortBox m C.bound,
      CarbonDoubleCount.Planner.IsFirstBest C.bound (profit C) C.footprint pS e → e = eStar)
    (hinterior : ∀ n j, 0 < eStar n j ∧ eStar n j < C.bound)
    (hrelevant : relevantIncidence C eStar)
    (hjoint : jointProduction C eStar)
    (hincreasing : ∀ n, MonotoneOn (R.payment n) (footprintOrthant I))
    (reservation : Fin N → ℝ)
    (hparticipation : participation C R reservation eStar)
    (hnash : isNash C R eStar) :
    ∃ i, pS < aggregateMarginal R (C.footprint eStar) i := by sorry

end SupplyChainCarbon.Necessity
