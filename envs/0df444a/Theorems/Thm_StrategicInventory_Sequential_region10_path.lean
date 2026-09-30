-- Prove2me | Theorems.Thm_StrategicInventory_Sequential_region10_path
-- name    : StrategicInventory.Sequential.region10_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T05:37:24.837066+00:00
-- url     : https://prove2.me/theorems/6902c700-9878-40c3-8533-ad91979330ff
-- title:
--   Appendix A, Region 10 (second part) — no inventory when $h > h_7$ and $2\alpha/3 < s < 5\alpha/6$
-- statement:
--   Let $\alpha > 0$, $h \ge 0$ and $s \ge 0$, and let $h_7$ be the threshold of Appendix A. Suppose
--
--   $$
--   h_7 < h, \qquad \frac{2\alpha}{3} < s < \frac{5\alpha}{6},
--   $$
--
--   which is the second part of Region 10 in Table A.1. Then the sequential game has a subgame perfect equilibrium, and every subgame perfect equilibrium has the path of Table A.4, column 10:
--
--   $$
--   w_1 = \frac{\alpha}{2},\quad Q_1 = q_1 = \frac{\alpha}{4},\quad w_2 = \frac{3s - \alpha}{2},\quad Q_2 = q_2 = \alpha - s,\quad q_s = 0 .
--   $$
--
--   In particular the buyer holds no inventory. For a fixed $s < 5\alpha/6$, a large enough holding cost therefore removes strategic inventory. This is why the $\epsilon$ in Proposition 4.2 has to depend on $h$.
-- source:
--   Guan, Gurnani, Geng & Luo, Strategic Inventory and Supplier Encroachment, MSOM 21(3) 2019, pp. 551–553, Appendix A, Table A.1, Region 10, and Table A.4, Region 10

import Mathlib
import Definitions.Def_StrategicInventory_Sequential_Game
import Definitions.Def_StrategicInventory_Sequential_IsSPE
import Definitions.Def_StrategicInventory_Sequential_Thresholds

namespace StrategicInventory.Sequential

/-- Appendix A, Table A.1 Region 10 (second part) with Table A.4 column 10,
pp. 551–553: for `h7 < h` and `2α/3 < s < 5α/6`, a subgame perfect equilibrium
exists and every one has the path `w1 = α/2`, `Q1 = q1 = α/4`,
`w2 = (3s − α)/2`, `Q2 = q2 = α − s`, `qs = 0` (so `I = 0`). -/
theorem region10_path (α h s : ℝ) (hα : 0 < α) (hh : 0 ≤ h) (hs : 0 ≤ s)
    (hreg : h7 α s < h ∧ 2 * α / 3 < s ∧ s < 5 * α / 6) :
    (∃ σ : Profile, IsSPE α h s σ) ∧
      ∀ σ : Profile, IsSPE α h s σ →
        σ.path = { w1 := α / 2, Q1 := α / 4, q1 := α / 4,
                   w2 := (3 * s - α) / 2, Q2 := α - s, q2 := α - s,
                   qs := 0 } := by sorry

end StrategicInventory.Sequential
