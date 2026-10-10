-- Prove2me | Theorems.Thm_SupplyDemand_equilibrium_unique
-- name    : SupplyDemand.equilibrium_unique
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:44.595976+00:00
-- url     : https://prove2.me/theorems/7da012b8-d1f2-4ae1-97e5-81d90d04e3f2
-- title:
--   Uniqueness of the market equilibrium
-- statement:
--   Let $I\subseteq\mathbb R$ be a set of admissible prices, let $S$ be a supply curve that is strictly increasing on $I$, and let $D$ be a demand curve that is strictly decreasing on $I$. If $(p_1,q_1)$ and $(p_2,q_2)$ are both market equilibria of $(S,D)$ with $p_1,p_2\in I$, then
--   $$p_1=p_2\quad\text{and}\quad q_1=q_2.$$
--
--   So, for upward-sloping supply and downward-sloping demand, the equilibrium is "the" intersection of the two curves, as the source describes it.
--
--   **Formalization Note** Curves are functions $\mathbb R\to\mathbb R$; the slope assumptions are imposed on an arbitrary set $I$ of admissible prices, and all equilibrium prices are assumed to lie in $I$.
-- source:
--   Wikipedia, "Supply and demand", revision 1378800284, https://en.wikipedia.org/w/index.php?title=Supply_and_demand&oldid=1378800284, section "Equilibrium" and "Market equilibrium"

import Mathlib
import Definitions.Def_SupplyDemand_Model

namespace SupplyDemand

theorem equilibrium_unique (I : Set ℝ) (S D : ℝ → ℝ)
    (hS : StrictMonoOn S I) (hD : StrictAntiOn D I)
    {p₁ q₁ p₂ q₂ : ℝ} (hp₁ : p₁ ∈ I) (hp₂ : p₂ ∈ I)
    (h₁ : IsEquilibrium S D p₁ q₁) (h₂ : IsEquilibrium S D p₂ q₂) :
    p₁ = p₂ ∧ q₁ = q₂ := by sorry

end SupplyDemand
