-- Prove2me | Theorems.Thm_StrategicInventory_Sequential_inventory_near_five_sixths
-- name    : StrategicInventory.Sequential.inventory_near_five_sixths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T05:44:39.05956+00:00
-- url     : https://prove2.me/theorems/3a10e251-13a1-45ac-b691-ff48f856c4c3
-- title:
--   Proposition 4.2 — for any $h > 0$ the buyer withholds inventory for $s$ just below $5/6$, at total holding cost below $11/72$
-- statement:
--   Normalize the demand intercept to $\alpha = 1$, as the paper does from §4 on. For every holding cost $h > 0$ there is an $\epsilon > 0$ such that the following holds for every direct selling cost $s \in (5/6 - \epsilon, 5/6)$:
--
--   1. the sequential two-period game has a subgame perfect equilibrium;
--   2. in every subgame perfect equilibrium, the buyer's inventory $I = Q_1 - q_1$ on the equilibrium path satisfies
--
--   $$
--   I > 0 \qquad\text{and}\qquad h\, I < \frac{11}{72}.
--   $$
--
--   The inventory $I$ is read off the path of a subgame perfect equilibrium of the game of §2.1. It is not given by a closed-form expression. When the supplier can sell directly only at a cost just below $5/6$, the buyer withholds strategic inventory however large its holding cost is. This contrasts with the model without a direct channel (Anand et al. 2008), where no inventory is held once $h \ge 1/4$. Even for large $h$, the buyer's total holding cost stays below the constant $11/72$.
--
--   **Formalization Note.** Existence of an equilibrium is stated explicitly. Without it, the claim about every equilibrium would hold vacuously if none existed. The paper speaks of "the" equilibrium; the statement here quantifies over every subgame perfect equilibrium, which is the same claim whenever the equilibrium path is unique. The bound $11/72$ is asserted for the same $h$ and $s$ as the positivity of $I$. The quantifier order is "for all $h$, there exists $\epsilon$": $\epsilon$ may depend on $h$.
-- source:
--   Guan, Gurnani, Geng & Luo, Strategic Inventory and Supplier Encroachment, MSOM 21(3) 2019, p. 546, Proposition 4.2 (normalization α = 1 from §4, p. 542)

import Mathlib
import Definitions.Def_StrategicInventory_Sequential_Game
import Definitions.Def_StrategicInventory_Sequential_IsSPE

namespace StrategicInventory.Sequential

/-- Proposition 4.2, p. 546 (with the normalization `α = 1` of §4, p. 542):
for any `h > 0` there is `ε > 0` such that for every `s ∈ (5/6 − ε, 5/6)` a
subgame perfect equilibrium exists, and in every subgame perfect equilibrium the
buyer's inventory `I` is positive and its total inventory cost `h I` is less
than `11/72`. -/
theorem inventory_near_five_sixths :
    ∀ h : ℝ, 0 < h → ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Set.Ioo (5 / 6 - ε) (5 / 6),
      (∃ σ : Profile, IsSPE 1 h s σ) ∧
        ∀ σ : Profile, IsSPE 1 h s σ →
          0 < σ.path.inventory ∧ h * σ.path.inventory < 11 / 72 := by sorry

end StrategicInventory.Sequential
