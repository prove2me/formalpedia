-- Prove2me | Theorems.Thm_SupplyDemand_ibn_taymiyyah
-- name    : SupplyDemand.ibn_taymiyyah
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:33.082567+00:00
-- url     : https://prove2.me/theorems/7ece2572-81f0-42b3-b41c-235637919f97
-- title:
--   Simultaneous shifts: Ibn Taymiyyah's law of price
-- statement:
--   Let $I\subseteq\mathbb R$ be a set of admissible prices. Let $S_1,S_2$ be supply curves strictly increasing on $I$ and $D_1,D_2$ demand curves strictly decreasing on $I$. Let $(p_1,q_1)$ be a market equilibrium of $(S_1,D_1)$ and $(p_2,q_2)$ a market equilibrium of $(S_2,D_2)$, with $p_1,p_2\in I$. Then:
--
--   1. if demand increases ($D_1<D_2$ on $I$) while supply decreases ($S_2<S_1$ on $I$), then $p_1<p_2$;
--   2. if demand decreases ($D_2<D_1$ on $I$) while supply increases ($S_1<S_2$ on $I$), then $p_2<p_1$.
--
--   This is the precise form of the quotation "If desire for goods increases while its availability decreases, its price rises. On the other hand, if availability of the good increases and the desire for it decreases, the price comes down." Nothing is asserted about the quantity, whose direction is undetermined.
--
--   **Formalization Note** Curves are functions $\mathbb R\to\mathbb R$; the slope assumptions are imposed on an arbitrary set $I$ of admissible prices, and all equilibrium prices are assumed to lie in $I$.
-- source:
--   Wikipedia, "Supply and demand", revision 1378800284, https://en.wikipedia.org/w/index.php?title=Supply_and_demand&oldid=1378800284, section "History" (quotation of Ibn Taymiyyah)

import Mathlib
import Definitions.Def_SupplyDemand_Model

namespace SupplyDemand

theorem ibn_taymiyyah (I : Set ℝ) (S₁ S₂ D₁ D₂ : ℝ → ℝ)
    (hS₁ : StrictMonoOn S₁ I) (hS₂ : StrictMonoOn S₂ I)
    (hD₁ : StrictAntiOn D₁ I) (hD₂ : StrictAntiOn D₂ I)
    {p₁ q₁ p₂ q₂ : ℝ} (hp₁ : p₁ ∈ I) (hp₂ : p₂ ∈ I)
    (h₁ : IsEquilibrium S₁ D₁ p₁ q₁) (h₂ : IsEquilibrium S₂ D₂ p₂ q₂) :
    ((∀ p ∈ I, D₁ p < D₂ p) → (∀ p ∈ I, S₂ p < S₁ p) → p₁ < p₂) ∧
    ((∀ p ∈ I, D₂ p < D₁ p) → (∀ p ∈ I, S₁ p < S₂ p) → p₂ < p₁) := by sorry

end SupplyDemand
