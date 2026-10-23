-- Prove2me | Theorems.Thm_StaticReusable_Guarantee_theorem_1
-- name    : StaticReusable.Guarantee.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:36.449305+00:00
-- url     : https://prove2.me/theorems/20f68cae-2b7b-4449-b5a4-ff7ecca83515
-- title:
--   Theorem 1, p. 11 — some static price attains 15/19 of the profit rate, market share and service level of every optimal stationary dynamic policy
-- statement:
--   Let $(C, \mu, \Lambda, c, p, \alpha_1, \alpha_2, \alpha_3)$ be an instance of the class $\Omega$: $C \ge 1$ units, $\mu, \Lambda, c > 0$, weights $\alpha_i \ge 0$ summing to $1$, a profit rate $\lambda(p(\lambda) - c)$ concave on $[0,\Lambda]$ and $p$ strictly decreasing on $(0,\Lambda]$. Let $\pi^* = (\lambda^*_1, \dots, \lambda^*_C)$ be an optimal dynamic pricing policy: a stationary policy with rates in $[0,\Lambda]$ that maximizes $\alpha_1 \mathcal P^\pi + \alpha_2 \mathcal{MS}^\pi + \alpha_3 \mathcal{SL}^\pi$ over all such policies. Then there is a static policy $\pi^s$, with a single rate $l \in [0,\Lambda]$ used in every state, such that
--
--   1. $\mathcal P^{\pi^s} \ge \frac{15}{19}\,\mathcal P^{\pi^*}$ whenever $\mathcal P^{\pi^*} \ge 0$;
--   2. $\mathcal{MS}^{\pi^s} \ge \frac{15}{19}\,\mathcal{MS}^{\pi^*}$;
--   3. $\mathcal{SL}^{\pi^s} \ge \frac{15}{19}\,\mathcal{SL}^{\pi^*}$.
--
--   Equivalently, wherever the ratios are defined,
--   $$\inf_{\Omega} \min\left\{\frac{\mathcal P^{\pi^s}}{\mathcal P^{\pi^*}}, \frac{\mathcal{MS}^{\pi^s}}{\mathcal{MS}^{\pi^*}}, \frac{\mathcal{SL}^{\pi^s}}{\mathcal{SL}^{\pi^*}}\right\} \ge \frac{15}{19}.$$
--
--   A single price, chosen once, thus loses at most about $21\%$ of each of the three objectives relative to the best state-dependent pricing, for every number of units, service rate, demand curve and weighting of the objectives.
--
--   **Formalization Note** Policies are the stationary state-dependent policies of §2.3 with the closed-form steady state; "the optimal dynamic pricing policy" is read as *every* maximizer (`IsMaxOn` over the policies with rates in $[0,\Lambda]$), and existence of a maximizer is not asserted. The three bounds are stated as inequalities rather than ratios, so that no division by a zero objective occurs. The profit bound is conditional on $\mathcal P^{\pi^*} \ge 0$: when the weights favour market share, the optimal policy may price below cost, its profit is negative, and the profit ratio of the page has no meaning.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, p. 11, Theorem 1

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace StaticReusable.Guarantee

theorem theorem_1 {C : ℕ} {μ Λ c α₁ α₂ α₃ : ℝ} {p : ℝ → ℝ}
    (hS : Standing C μ Λ c p α₁ α₂ α₃) (lamStar : ℕ → ℝ) (hpol : lamStar ∈ Policies C Λ)
    (hopt : IsMaxOn (value C μ p c α₁ α₂ α₃) (Policies C Λ) lamStar) :
    ∃ l ∈ Set.Icc 0 Λ,
      (0 ≤ profit C μ p c lamStar →
          (15 / 19 : ℝ) * profit C μ p c lamStar ≤ profit C μ p c (fun _ => l)) ∧
        (15 / 19 : ℝ) * marketShare C μ lamStar ≤ marketShare C μ (fun _ => l) ∧
        (15 / 19 : ℝ) * serviceLevel C μ lamStar ≤ serviceLevel C μ (fun _ => l) := by sorry
end StaticReusable.Guarantee
