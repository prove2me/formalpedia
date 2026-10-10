-- Prove2me | Theorems.Thm_SupplyDemand_supply_increase
-- name    : SupplyDemand.supply_increase
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:57.410052+00:00
-- url     : https://prove2.me/theorems/ff9df667-09cc-47f8-a864-98ea9c6aa94c
-- title:
--   An increase in supply lowers equilibrium price and raises quantity
-- statement:
--   Let $I\subseteq\mathbb R$ be a set of admissible prices. Let $S_1,S_2$ be supply curves strictly increasing on $I$, with supply increasing from $S_1$ to $S_2$: $S_1(p)<S_2(p)$ for all $p\in I$, and let $D$ be a demand curve strictly decreasing on $I$. If $(p_1,q_1)$ is a market equilibrium of $(S_1,D)$ and $(p_2,q_2)$ is a market equilibrium of $(S_2,D)$, with $p_1,p_2\in I$, then
--   $$p_2<p_1\quad\text{and}\quad q_1<q_2.$$
--
--   After a supply shift, price and quantity move in opposite directions; read with the indices exchanged, a left shift raises the price and lowers the quantity.
--
--   **Formalization Note** Curves are functions $\mathbb R\to\mathbb R$; the slope assumptions are imposed on an arbitrary set $I$ of admissible prices, and all equilibrium prices are assumed to lie in $I$.
-- source:
--   Wikipedia, "Supply and demand", revision 1378800284, https://en.wikipedia.org/w/index.php?title=Supply_and_demand&oldid=1378800284, section "Supply curve shifts"

import Mathlib
import Definitions.Def_SupplyDemand_Model

namespace SupplyDemand

theorem supply_increase (I : Set ℝ) (S₁ S₂ D : ℝ → ℝ)
    (hS₁ : StrictMonoOn S₁ I) (hS₂ : StrictMonoOn S₂ I) (hD : StrictAntiOn D I)
    (hshift : ∀ p ∈ I, S₁ p < S₂ p)
    {p₁ q₁ p₂ q₂ : ℝ} (hp₁ : p₁ ∈ I) (hp₂ : p₂ ∈ I)
    (h₁ : IsEquilibrium S₁ D p₁ q₁) (h₂ : IsEquilibrium S₂ D p₂ q₂) :
    p₂ < p₁ ∧ q₁ < q₂ := by sorry

end SupplyDemand
