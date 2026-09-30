-- Prove2me | Theorems.Thm_StrategicInventory_Sequential_region8_path
-- name    : StrategicInventory.Sequential.region8_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T05:19:12.864494+00:00
-- url     : https://prove2.me/theorems/6ccab412-0fb0-4505-a667-b62d4b2e420d
-- title:
--   Appendix A, Region 8 — the equilibrium path with inventory $I = 5(\alpha - 4h)/34$
-- statement:
--   Let $\alpha > 0$, $h \ge 0$ and $s \ge 0$, and let $s_3$ and $h_{11}$ be the thresholds of Appendix A (with $s_3$ corrected, see the definition file). Suppose $(h, s)$ lies in Region 8 of Table A.1, with the boundary $h = h_{11}$ removed:
--
--   $$
--   \Big(h < h_{11},\ s_3 \le s < \tfrac{5\alpha}{6}\Big) \quad\text{or}\quad \Big(h < \tfrac{\alpha}{4},\ \tfrac{5\alpha}{6} \le s < \alpha\Big).
--   $$
--
--   Then the sequential game has a subgame perfect equilibrium, and every subgame perfect equilibrium has the path of Table A.4, column 8:
--
--   $$
--   w_1 = \frac{9\alpha - 2h}{17},\quad Q_1 = \frac{13\alpha - 18h}{34},\quad q_1 = \frac{4\alpha + h}{17},\quad
--   w_2 = \frac{2(3\alpha + 5h)}{17},\quad Q_2 = \frac{3\alpha + 5h}{17},\quad q_2 = \frac{11\alpha - 10h}{34},\quad q_s = 0 .
--   $$
--
--   In particular the buyer withholds the inventory $I = Q_1 - q_1 = 5(\alpha - 4h)/34$, and the supplier does not sell directly. This is the regime of Proposition 4.2 when the holding cost is small.
--
--   **Formalization Note.** The printed region includes $h = h_{11}$. There the supplier's Region 8 and Region 7 profits coincide (numerically, $\approx 0.25418$ at $\alpha = 1$, $s = 0.8$) while the two paths differ, so the equilibrium path need not be unique. That boundary is therefore excluded. The boundary $s = s_3$ is kept: the first part of Region 7 is printed as $s_2 \le s < s_3$, so it does not overlap Region 8.
-- source:
--   Guan, Gurnani, Geng & Luo, Strategic Inventory and Supplier Encroachment, MSOM 21(3) 2019, pp. 551–553, Appendix A, Table A.1, Region 8, and Table A.4, Region 8

import Mathlib
import Definitions.Def_StrategicInventory_Sequential_Game
import Definitions.Def_StrategicInventory_Sequential_IsSPE
import Definitions.Def_StrategicInventory_Sequential_Thresholds

namespace StrategicInventory.Sequential

/-- Appendix A, Table A.1 Region 8 with Table A.4 column 8, pp. 551–553: for
`(h, s)` with `0 ≤ h < h11, s3 ≤ s < 5α/6` (corrected `s3`; the boundary
`h = h11` of the printed region is excluded) or
`0 ≤ h < α/4, 5α/6 ≤ s < α`, a subgame perfect equilibrium exists and every
one has the path `w1 = (9α − 2h)/17`, `Q1 = (13α − 18h)/34`, `q1 = (4α + h)/17`,
`w2 = 2(3α + 5h)/17`, `Q2 = (3α + 5h)/17`, `q2 = (11α − 10h)/34`, `qs = 0`
(so `I = 5(α − 4h)/34`). -/
theorem region8_path (α h s : ℝ) (hα : 0 < α) (hh : 0 ≤ h) (hs : 0 ≤ s)
    (hreg : (h < h11 α s ∧ s3 α ≤ s ∧ s < 5 * α / 6) ∨
      (h < α / 4 ∧ 5 * α / 6 ≤ s ∧ s < α)) :
    (∃ σ : Profile, IsSPE α h s σ) ∧
      ∀ σ : Profile, IsSPE α h s σ →
        σ.path = { w1 := (9 * α - 2 * h) / 17, Q1 := (13 * α - 18 * h) / 34,
                   q1 := (4 * α + h) / 17, w2 := 2 * (3 * α + 5 * h) / 17,
                   Q2 := (3 * α + 5 * h) / 17, q2 := (11 * α - 10 * h) / 34,
                   qs := 0 } := by sorry

end StrategicInventory.Sequential
