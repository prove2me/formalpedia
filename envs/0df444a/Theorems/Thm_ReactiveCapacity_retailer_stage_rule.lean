-- Prove2me | Theorems.Thm_ReactiveCapacity_retailer_stage_rule
-- name    : ReactiveCapacity.retailer_stage_rule
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:19:00.752053+00:00
-- url     : https://prove2.me/theorems/f70e5b3d-0937-4579-9b0f-d881df25b820
-- title:
--   Retailer's step-one rule: high price in the good market, low price in the bad market iff $\Pi_L>\Pi_H(\alpha_b)$ (corrected: exact comparison, not the threshold on $I$)
-- statement:
--   Let the retailer have quality $q>0$ and wholesale price $0\le w<q\theta_H$, and suppose that in the season it can obtain up to $S\ge 0$ units, an order $Q$ yielding $\min\{Q,S\}$ units. Write
--   $$
--   \Pi_H(\alpha)=(q\theta_H-w)\min\{\alpha,S\},\qquad \Pi_L=(q\theta_L-w)\min\{S,1\}
--   $$
--   for the profits of targeting only the high-valuation consumers (price $q\theta_H$) and of targeting all consumers (price $q\theta_L$). Under the standing assumptions:
--
--   1. for every $\alpha\in[0,1]$, the retailer's best payoff over orders $Q\ge 0$ and prices $p\ge 0$ is $\max\{\Pi_H(\alpha),\Pi_L,0\}$;
--   2. in the good market, if $S>0$, every optimal choice has the high price $p=q\theta_H$;
--   3. in the bad market, if $\Pi_L>\Pi_H(\alpha_b)$, every optimal choice has the low price $p=q\theta_L$;
--   4. in the bad market, if $\Pi_L<\Pi_H(\alpha_b)$, every optimal choice has the high price $p=q\theta_H$.
--
--   With $S=\min\{I+\bar Q,1\}$ this is the comparison $(q\theta_H-w)\alpha_b$ versus $(q\theta_L-w)\min\{I+\bar Q,1\}$ of the Online Appendix: the retailer's step-one decision depends on the supplier's inventory only through the supply it makes available.
--
--   **Formalization Note** The supply $S$ stands for $I+\bar Q$ when the supplier fills every order up to its capacity, which it does when $w>kq^2$.
--
--   Differences from the source:
--   - correction: the summary rule "low price in the bad market iff $I>(\theta_H/\theta_L)\alpha_b-\bar Q$" (OA p.5) → the exact comparison of $\Pi_L$ and $\Pi_H(\alpha_b)$ derived on OA p.3; reason: the summary rule is false, e.g. $\theta_H=2,\theta_L=1,\alpha_b=0.4,\bar Q=0,I=0.81>0.8,q=1,w=1$ gives $\Pi_L=0<\Pi_H(\alpha_b)=0.4$, so the high price is optimal.
--   - generalization: the best payoff in the states $\alpha_g,\alpha_b$ → the best payoff for every $\alpha\in[0,1]$; reason: the same argument; it specializes to the two states.
--   - encoding: the supply $\min\{I+\bar Q,1\}$ of the game, any contract → an abstract supply $S\ge 0$, $S>0$ in the good market, and $0\le w<q\theta_H$; reason: with $S=0$ nothing is sold and every price is optimal, and with $w\ge q\theta_H$ no sale is profitable, so these cases have no price rule.
-- source:
--   Jiang–Tian, Effects of Reactive Capacity, SSRN 3308215 (version of May 5, 2022), Online Appendix §I.1, OA pp.2–3 (PDF 47–48), the comparison on OA p.3; summary OA p.5 (PDF 50)

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game

namespace ReactiveCapacity

/-- The retailer's step-one rule. Jiang–Tian, *Effects of Reactive Capacity*, SSRN 3308215
(version of May 5, 2022), Online Appendix §I.1, OA pp.2–5 (PDF 47–50).

Let `q > 0`, `0 ≤ w < qθ_H`, and let `S ≥ 0` be the supply the retailer can obtain in the season.
Write `Π_H(α) = (qθ_H − w) min[α, S]` (target only high-valuation consumers, price `qθ_H`) and
`Π_L = (qθ_L − w) min[S, 1]` (target all consumers, price `qθ_L`).

1. For every `α ∈ [0, 1]`, the retailer's best payoff over orders `Q ≥ 0` and prices `p ≥ 0` is
   `max{Π_H(α), Π_L, 0}`.
2. In the good market, if `S > 0`, every optimal choice has the high price `p = qθ_H`.
3. In the bad market, if `Π_L > Π_H(α_b)` every optimal choice has the low price `p = qθ_L`.
4. In the bad market, if `Π_L < Π_H(α_b)` every optimal choice has the high price `p = qθ_H`.

**Formalization Note** The supply `S` stands for `I + Q̄` when the supplier fills every order up to
its capacity (the case `w > kq²`); `Params.stepOnePayoff` receives `min[Q, S]`. The paper's summary
(OA p.5) states the bad-market rule as the threshold `I > (θ_H/θ_L)α_b − Q̄`; this statement uses
the exact comparison the paper derives on OA p.3, of which the threshold is not a consequence. -/
theorem retailer_stage_rule (P : Params) (hP : P.Standing) (q w S : ℝ) (hq : 0 < q) (hw0 : 0 ≤ w) (hw : w < q * P.θH) (hS : 0 ≤ S) :
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      IsGreatest {v : ℝ | ∃ Q p : ℝ, 0 ≤ Q ∧ 0 ≤ p ∧ v = P.stepOnePayoff q w α S Q p}
        (max (max ((q * P.θH - w) * min α S) ((q * P.θL - w) * min S 1)) 0)) ∧
    (0 < S → ∀ Q p : ℝ, 0 ≤ Q → 0 ≤ p →
      (∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' → P.stepOnePayoff q w P.αg S Q' p' ≤ P.stepOnePayoff q w P.αg S Q p) →
      p = q * P.θH) ∧
    ((q * P.θH - w) * min P.αb S < (q * P.θL - w) * min S 1 → ∀ Q p : ℝ, 0 ≤ Q → 0 ≤ p →
      (∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' → P.stepOnePayoff q w P.αb S Q' p' ≤ P.stepOnePayoff q w P.αb S Q p) →
      p = q * P.θL) ∧
    ((q * P.θL - w) * min S 1 < (q * P.θH - w) * min P.αb S → ∀ Q p : ℝ, 0 ≤ Q → 0 ≤ p →
      (∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' → P.stepOnePayoff q w P.αb S Q' p' ≤ P.stepOnePayoff q w P.αb S Q p) →
      p = q * P.θH) := by sorry

end ReactiveCapacity
