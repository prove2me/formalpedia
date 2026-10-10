-- Prove2me | Theorems.Thm_SupplyDemand_demand_increase
-- name    : SupplyDemand.demand_increase
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:21.920096+00:00
-- url     : https://prove2.me/theorems/40ca1b88-b742-4838-aaa3-2aada3cac377
-- title:
--   An increase in demand raises equilibrium price and quantity
-- statement:
--   Let $I\subseteq\mathbb R$ be a set of admissible prices. Let $S$ be a supply curve strictly increasing on $I$, and let $D_1,D_2$ be demand curves strictly decreasing on $I$, with demand increasing from $D_1$ to $D_2$: $D_1(p)<D_2(p)$ for all $p\in I$. If $(p_1,q_1)$ is a market equilibrium of $(S,D_1)$ and $(p_2,q_2)$ is a market equilibrium of $(S,D_2)$, with $p_1,p_2\in I$, then
--   $$p_1<p_2\quad\text{and}\quad q_1<q_2.$$
--
--   A right shift of the demand curve raises both the equilibrium price and the equilibrium quantity; read with the indices exchanged, a left shift lowers both.
--
--   **Formalization Note** Curves are functions $\mathbb R\to\mathbb R$; the slope assumptions are imposed on an arbitrary set $I$ of admissible prices, and all equilibrium prices are assumed to lie in $I$.
-- source:
--   Wikipedia, "Supply and demand", revision 1378800284, https://en.wikipedia.org/w/index.php?title=Supply_and_demand&oldid=1378800284, section "Demand curve shifts"

import Mathlib
import Definitions.Def_SupplyDemand_Model

namespace SupplyDemand

theorem demand_increase (I : Set ℝ) (S D₁ D₂ : ℝ → ℝ)
    (hS : StrictMonoOn S I) (hD₁ : StrictAntiOn D₁ I) (hD₂ : StrictAntiOn D₂ I)
    (hshift : ∀ p ∈ I, D₁ p < D₂ p)
    {p₁ q₁ p₂ q₂ : ℝ} (hp₁ : p₁ ∈ I) (hp₂ : p₂ ∈ I)
    (h₁ : IsEquilibrium S D₁ p₁ q₁) (h₂ : IsEquilibrium S D₂ p₂ q₂) :
    p₁ < p₂ ∧ q₁ < q₂ := by sorry

end SupplyDemand
