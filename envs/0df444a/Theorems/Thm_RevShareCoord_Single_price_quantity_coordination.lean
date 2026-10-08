-- Prove2me | Theorems.Thm_RevShareCoord_Single_price_quantity_coordination
-- name    : RevShareCoord.Single.price_quantity_coordination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:41:56.423531+00:00
-- url     : https://prove2.me/theorems/f23ba380-9784-4de1-b17e-c783c8075093
-- title:
--   Sec. 3.1, fn. 3 — with price a decision too, {φ, φc} gives π_r(q, p) = φΠ(q, p) and makes (q_I, p_I) the retailer's unique optimum
-- statement:
--   Let revenue $\mathrm{Rev}(q, p)$ be any function of the quantity $q$ and the retail price $p$, with costs linear in quantity at unit cost $c > 0$, so that the integrated channel earns $\Pi(q, p) = \mathrm{Rev}(q,p) - cq$. Let $P$ be the set of admissible prices and assume the integrated channel has a unique optimal pair $(q_I, p_I)$ over $q \ge 0$, $p \in P$. Let the supplier offer the revenue-sharing contract $\{\phi, \phi c\}$ with $\phi \in (0, 1]$. Then
--
--   1. for every $(q, p)$ the retailer's profit is a fixed share of the channel profit,
--   $$
--   \pi_r(q, p, \phi c, \phi) = \phi\,\Pi(q, p);
--   $$
--   2. $(q_I, p_I)$ maximizes the retailer's profit over $q \ge 0$, $p \in P$, and is the only pair that does.
--
--   So the retailer orders the supply chain's optimal quantity and sets its optimal price. The paper proves this for the price-dependent newsvendor, $\mathrm{Rev}(q,p) = p\bigl(q - \int_0^q F(x,p)\,dx\bigr)$, and notes in footnote 3 that the argument applies to any revenue function of price and quantity with linear costs, which is the generality stated here.
--
--   **Formalization Note.** The paper assumes (rather than derives) that the integrated optimum $(q_I, p_I)$ is unique, and this is a hypothesis. The paper's monotonicity assumption on $F(x, p)$ in $p$ is not used by the argument and is not part of the statement. The admissible price set $P$ is a parameter, since the paper does not restrict the price.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 11 (PDF p. 12), Section 3.1, display π_r(q, p, w, φ) = φΠ(q, p), and footnote 3

import Mathlib
import Definitions.Def_RevShareCoord_Single_PriceQuantity

namespace RevShareCoord.Single

/-- Sec. 3.1 and footnote 3, p. 11: let revenue `Rev(q, p)` be any function of quantity and
price, costs linear in quantity at unit cost `c`, and let `(q_I, p_I)` be the integrated channel's
unique optimal quantity–price pair over `q ≥ 0` and admissible prices `p ∈ P`. Under the
revenue-sharing contract `{φ, φc}` with `φ ∈ (0, 1]`, the retailer's profit is `φ` times the
integrated profit at every `(q, p)`, and `(q_I, p_I)` is the retailer's unique optimum. -/
theorem price_quantity_coordination (Rev : ℝ → ℝ → ℝ) (c φ : ℝ) (hc : 0 < c)
    (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (P : Set ℝ) (qI pI : ℝ) (hqI : 0 ≤ qI) (hpI : pI ∈ P)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => pqChainProfit Rev c x.1 x.2) (Set.Ici 0 ×ˢ P) (qI, pI))
    (huniq : ∀ x ∈ Set.Ici (0 : ℝ) ×ˢ P,
      IsMaxOn (fun x : ℝ × ℝ => pqChainProfit Rev c x.1 x.2) (Set.Ici 0 ×ˢ P) x → x = (qI, pI)) :
    (∀ q p : ℝ, pqRetailerProfit Rev φ (φ * c) q p = φ * pqChainProfit Rev c q p) ∧
    IsMaxOn (fun x : ℝ × ℝ => pqRetailerProfit Rev φ (φ * c) x.1 x.2) (Set.Ici 0 ×ˢ P) (qI, pI) ∧
    ∀ x ∈ Set.Ici (0 : ℝ) ×ˢ P,
      IsMaxOn (fun x : ℝ × ℝ => pqRetailerProfit Rev φ (φ * c) x.1 x.2) (Set.Ici 0 ×ˢ P) x →
        x = (qI, pI) := by sorry

end RevShareCoord.Single
