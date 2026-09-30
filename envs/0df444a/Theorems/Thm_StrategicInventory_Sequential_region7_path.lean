-- Prove2me | Theorems.Thm_StrategicInventory_Sequential_region7_path
-- name    : StrategicInventory.Sequential.region7_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T05:29:12.993965+00:00
-- url     : https://prove2.me/theorems/6c70e567-9b1d-4d33-b7c5-a504ceed11e0
-- title:
--   Appendix A, Region 7 (second part) — the equilibrium path with inventory $I^* = (2\alpha - 3s + x)/2$
-- statement:
--   Let $\alpha > 0$, $h \ge 0$ and $s \ge 0$, and let $x$, $s_3$, $h_{10}$, $h_{11}$ and $I^* = (2\alpha - 3s + x)/2$ be as in Appendix A (with $s_3$ corrected). Suppose
--
--   $$
--   h_{11} < h < h_{10}, \qquad s_3 \le s < \frac{5\alpha}{6},
--   $$
--
--   which is the second part of Region 7 in Table A.1, with the boundary $h = h_{10}$ removed. Then the sequential game has a subgame perfect equilibrium, and every subgame perfect equilibrium has the path of Table A.3, column 7. Writing $I = I^*$, that path is
--
--   $$
--   w_1 = \frac{\alpha + 2I}{2},\quad Q_1 = I + \frac{\alpha - w_1}{2},\quad q_1 = \frac{\alpha - w_1}{2},\quad
--   w_2 = \frac{\alpha - 2I}{2},\quad Q_2 = \frac{\alpha - 2I}{4},\quad q_2 = \frac{\alpha + 2I}{4},\quad q_s = 0 .
--   $$
--
--   So the buyer withholds exactly $I^*$ units, and the supplier keeps its direct channel as a threat without using it. This is the regime of Proposition 4.2 when the holding cost is large.
--
--   **Formalization Note.** The first part of Region 7 ($s_2 \le s < s_3$, $h \le \min\{h_9, h_{10}\}$) involves the implicitly defined root $s_2$ and is not stated. The printed region includes $h = h_{10}$. There the path switches to Region 6, with no inventory. As a precaution against non-uniqueness at the switching point, that boundary is excluded.
-- source:
--   Guan, Gurnani, Geng & Luo, Strategic Inventory and Supplier Encroachment, MSOM 21(3) 2019, pp. 551–553, Appendix A, Table A.1, Region 7, and Table A.3, Region 7

import Mathlib
import Definitions.Def_StrategicInventory_Sequential_Game
import Definitions.Def_StrategicInventory_Sequential_IsSPE
import Definitions.Def_StrategicInventory_Sequential_Thresholds

namespace StrategicInventory.Sequential

/-- Appendix A, Table A.1 Region 7 (second part) with Table A.3 column 7,
pp. 551–553: for `h11 < h < h10` and `s3 ≤ s < 5α/6` (corrected `s3`; the
boundary `h = h10` of the printed region is excluded), a subgame perfect
equilibrium exists and every one has the path with `I = I* = (2α − 3s + x)/2`,
`w1 = (α + 2I)/2`, `Q1 = I + (α − w1)/2`, `q1 = (α − w1)/2`, `w2 = (α − 2I)/2`,
`Q2 = (α − 2I)/4`, `q2 = (α + 2I)/4`, `qs = 0`. -/
theorem region7_path (α h s : ℝ) (hα : 0 < α) (hh : 0 ≤ h) (hs : 0 ≤ s)
    (hreg : h11 α s < h ∧ h < h10 α s ∧ s3 α ≤ s ∧ s < 5 * α / 6) :
    (∃ σ : Profile, IsSPE α h s σ) ∧
      ∀ σ : Profile, IsSPE α h s σ →
        σ.path = { w1 := (α + 2 * invStar α s) / 2,
                   Q1 := invStar α s + (α - (α + 2 * invStar α s) / 2) / 2,
                   q1 := (α - (α + 2 * invStar α s) / 2) / 2,
                   w2 := (α - 2 * invStar α s) / 2,
                   Q2 := (α - 2 * invStar α s) / 4,
                   q2 := (α + 2 * invStar α s) / 4,
                   qs := 0 } := by sorry

end StrategicInventory.Sequential
