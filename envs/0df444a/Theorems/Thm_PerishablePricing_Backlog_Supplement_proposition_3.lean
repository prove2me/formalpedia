-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_Supplement_proposition_3
-- name    : PerishablePricing.Backlog.Supplement.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:01:34.683803+00:00
-- url     : https://prove2.me/theorems/159cda61-0806-4da8-9d04-e30046487285
-- title:
--   Proposition 3, p. 293 — L♮-concavity of revenue, with its necessary demand-range degeneracy
-- statement:
--   For each source carrier $\mathbb F\in\{\mathbb R,\mathbb Z\}$, let $\mathcal D$, $P$ and $\mu$ obey the §3 demand assumptions and the corresponding carrier conditions (C1) and (C2). The integer instance has integer expected-demand endpoints and integer additive noise. Then the full truncated-revenue conclusion holds, together with the derived singleton consequence:
--
--   $$\underline d=\bar d,\qquad
--   R(d,y)=P(d)\mathbb E_\mu[\min(d+\varepsilon,y)]
--   \quad\text{is L♮-concave on }(\mathcal D\cap\mathbb F)\times\mathbb F_+.$$
--
--   This retains every revenue/inventory input of each carrier. The singleton conclusion exposes an obstruction to applying these sufficient conditions to variable pricing; it is not an extra hypothesis. DISPROOF.md explains the obstruction and the limited scope of the support-only counterexample.
--
--   **Formalization Note** The integer half tests (C1) and (C2) only at integer decision points, with the same ordinary ambient derivatives of the actual price and CDF, not finite differences; positive-tail CDF jumps fail differentiability. The real half retains all real tests. Both halves omit only undefined zero-survival hazards, keeping all below-support tests. The revenue is stationary, so the printed time label adds no parameter. No inventory cost or Assumption 1 is assumed.
--
--   Differences from the source:
--   - reading: (C2) divides by $\bar F(y-d)$ for all $y\ge0$ → (C2) is tested for all $y\ge0$ with $\bar F(y-d)>0$, with the derivatives and nonzero price derivative required where used; reason: the quotient is undefined beyond the upper support; this is the domain of a hazard rate, and retains all points below the lower support
--   - generalization: the conditional L♮-concavity conclusion → the same conclusion together with $\underline d=\bar d$; reason: bounded support and $\underline d+A\ge0$ make (C2) impossible when $\underline d<\bar d$; a separate sorry-free local proof checks this consequence
--   - encoding: the revenue statement for $t=1,\ldots,T$ → one stationary revenue function with no time parameter; reason: there is no $t$ in the formula for $R$
--   - reading: the real/integer carrier convention and the discrete-demand claim → a separate integer revenue conjunct with integer expected-demand endpoints, almost-sure integer additive noise, and C1/C2 tested at integer decisions using ordinary derivatives; reason: integer expected demand and (1) make integer realized demand equivalent to integer noise; derivative-based C2 is not silently replaced by finite differences or extended to extra real test points
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, https://doi.org/10.1287/opre.2014.1261, Proposition 3 and (C1)–(C2), p. 293 (PDF 11); §3 demand support p. 288 (PDF 6)

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Supplement_IntegerDemand

namespace PerishablePricing.Backlog.Supplement

/-- Proposition 3 with its full conclusion and the necessary degeneracy consequence.
In particular these assumptions admit no strictly positive-width demand interval. -/
theorem proposition_3 :
    (∀ (Q : DemandData), Q.C1 → Q.C2 →
      Q.dlo = Q.dhi ∧ LNatConcaveOn Q.revenueDomain Q.revenueJoint) ∧
    (∀ (Q : IntegerDemandData), Q.C1 → Q.C2 →
      Q.lower = Q.upper ∧ LNatConcaveOnZ Q.revenueDomain Q.revenueJoint) := by sorry

end PerishablePricing.Backlog.Supplement
