-- Prove2me | Theorems.Thm_SupplyDemand_comparative_statics
-- name    : SupplyDemand.comparative_statics
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:35:52.335924+00:00
-- url     : https://prove2.me/theorems/f826412c-2152-46cc-9428-629c51c81cbf
-- title:
--   Comparative statics of supply and demand
-- statement:
--   Fix a set $I\subseteq\mathbb R$ of admissible prices. Supply curves are assumed strictly increasing on $I$ and demand curves strictly decreasing on $I$; all equilibrium prices are assumed to lie in $I$.
--
--   1. **Demand shift.** If $D_1(p)<D_2(p)$ for all $p\in I$, $(p_1,q_1)$ is an equilibrium of $(S,D_1)$ and $(p_2,q_2)$ is an equilibrium of $(S,D_2)$, then
--   $$p_1<p_2\quad\text{and}\quad q_1<q_2.$$
--   2. **Supply shift.** If $S_1(p)<S_2(p)$ for all $p\in I$, $(p_1,q_1)$ is an equilibrium of $(S_1,D)$ and $(p_2,q_2)$ is an equilibrium of $(S_2,D)$, then
--   $$p_2<p_1\quad\text{and}\quad q_1<q_2.$$
--
--   An increase in demand raises both equilibrium price and quantity; an increase in supply lowers the price and raises the quantity. The statements for decreases are obtained by exchanging the indices.
--
--   **Formalization Note** Curves are functions $\mathbb R\to\mathbb R$; the slope assumptions are imposed on an arbitrary set $I$ of admissible prices, and all equilibrium prices are assumed to lie in $I$.
-- source:
--   Wikipedia, "Supply and demand", revision 1378800284, https://en.wikipedia.org/w/index.php?title=Supply_and_demand&oldid=1378800284, section "Changes in market equilibrium", "Demand curve shifts", "Supply curve shifts"

import Mathlib
import Definitions.Def_SupplyDemand_Model

namespace SupplyDemand

theorem comparative_statics (I : Set ℝ) :
    (∀ (S D₁ D₂ : ℝ → ℝ), StrictMonoOn S I → StrictAntiOn D₁ I → StrictAntiOn D₂ I →
      (∀ p ∈ I, D₁ p < D₂ p) →
      ∀ p₁ q₁ p₂ q₂ : ℝ, p₁ ∈ I → p₂ ∈ I →
        IsEquilibrium S D₁ p₁ q₁ → IsEquilibrium S D₂ p₂ q₂ →
        p₁ < p₂ ∧ q₁ < q₂) ∧
    (∀ (S₁ S₂ D : ℝ → ℝ), StrictMonoOn S₁ I → StrictMonoOn S₂ I → StrictAntiOn D I →
      (∀ p ∈ I, S₁ p < S₂ p) →
      ∀ p₁ q₁ p₂ q₂ : ℝ, p₁ ∈ I → p₂ ∈ I →
        IsEquilibrium S₁ D p₁ q₁ → IsEquilibrium S₂ D p₂ q₂ →
        p₂ < p₁ ∧ q₁ < q₂) := by sorry

end SupplyDemand
