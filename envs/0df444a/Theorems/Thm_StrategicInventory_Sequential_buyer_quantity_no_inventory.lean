-- Prove2me | Theorems.Thm_StrategicInventory_Sequential_buyer_quantity_no_inventory
-- name    : StrategicInventory.Sequential.buyer_quantity_no_inventory
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T04:58:43.866067+00:00
-- url     : https://prove2.me/theorems/dc38a8c2-f8ec-47c7-9f2f-f333596d38ae
-- title:
--   §3.1.1, Eq. (1) — the buyer's period-2 selling quantity $q_b(w)$ without inventory
-- statement:
--   Consider the sequential two-period game with demand intercept $\alpha > 0$, holding cost $h \ge 0$ and direct selling cost $0 \le s < \alpha$. Let $\sigma$ be any subgame perfect equilibrium. Take any history in which the buyer carries no inventory ($Q_1 = q_1 \ge 0$), the supplier quoted $w_1 \ge 0$, and the period-2 wholesale price is $w \ge 0$. At that history the buyer's period-2 selling quantity is
--
--   $$
--   q_b(w) =
--   \begin{cases}
--   \dfrac{\alpha - w}{2} & \text{if } 0 \le w < (2s - \alpha)^+,\\[4pt]
--   \alpha - s & \text{if } (2s - \alpha)^+ \le w \le \dfrac{(3s - \alpha)^+}{2},\\[4pt]
--   \dfrac{\alpha + s - 2w}{2} & \text{if } \dfrac{(3s - \alpha)^+}{2} < w < \dfrac{\alpha + s}{2},\\[4pt]
--   0 & \text{if } \dfrac{\alpha + s}{2} \le w,
--   \end{cases}
--   $$
--
--   except at the single corner $w = 0$, $s < \alpha/3$, which is excluded.
--
--   The formula describes how the threat of direct selling shapes the buyer's period-2 decision. In the second branch the buyer sells exactly $\alpha - s$, the smallest quantity that keeps the supplier's direct channel shut.
--
--   **Formalization Note.** At $w = 0$ and $s < \alpha/3$ the printed second branch applies, because both of its bounds are $0$. It gives $\alpha - s$, whereas the buyer's unique optimum there is $(\alpha + s)/2$. For example, at $s = 0$ selling $\alpha$ yields price $0$ and profit $0$, while selling $\alpha/2$ yields a positive profit. The hypothesis "$w > 0$ or $s \ge \alpha/3$" excludes exactly that corner. The four cases are written in Lean as nested `if`s tested in the page's order. For $s < \alpha$ the page's intervals are consecutive and cover $[0, \infty)$, so the nested form is the same function. Only the selling quantity $q_2$ is determined; at $w = 0$ the order $Q_2$ is not.
-- source:
--   Guan, Gurnani, Geng & Luo, Strategic Inventory and Supplier Encroachment, MSOM 21(3) 2019, p. 540, §3.1.1, Eq. (1)

import Mathlib
import Definitions.Def_StrategicInventory_Sequential_Game
import Definitions.Def_StrategicInventory_Sequential_IsSPE

namespace StrategicInventory.Sequential

/-- §3.1.1, Eq. (1), p. 540: in every subgame perfect equilibrium, at every
history with no inventory (`Q1 = q1`) and period-2 wholesale price `w ≥ 0`, the
buyer's period-2 selling quantity is `qb(w)`:
`(α − w)/2` if `w < (2s − α)⁺`; `α − s` if `(2s − α)⁺ ≤ w ≤ (3s − α)⁺/2`;
`(α + s − 2w)/2` if `(3s − α)⁺/2 < w < (α + s)/2`; `0` if `(α + s)/2 ≤ w`.
The corner `w = 0, s < α/3` is excluded: there the printed second branch gives
`α − s`, while the buyer's unique optimum is `(α + s)/2`. -/
theorem buyer_quantity_no_inventory (α h s : ℝ) (hα : 0 < α) (hh : 0 ≤ h) (hs : 0 ≤ s)
    (hsα : s < α) (σ : Profile) (hσ : IsSPE α h s σ)
    (w1 Q1 w : ℝ) (hw1 : 0 ≤ w1) (hQ1 : 0 ≤ Q1) (hw : 0 ≤ w)
    (hcorner : 0 < w ∨ α / 3 ≤ s) :
    (σ.period2 w1 Q1 Q1 w).2 =
      if w < max (2 * s - α) 0 then (α - w) / 2
      else if w ≤ max (3 * s - α) 0 / 2 then α - s
      else if w < (α + s) / 2 then (α + s - 2 * w) / 2
      else 0 := by sorry

end StrategicInventory.Sequential
