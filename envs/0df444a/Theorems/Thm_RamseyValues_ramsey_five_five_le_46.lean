-- Prove2me | Theorems.Thm_RamseyValues_ramsey_five_five_le_46
-- name    : RamseyValues.ramsey_five_five_le_46
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T00:15:20.953552+00:00
-- url     : https://prove2.me/theorems/6bbeb47f-65fe-42f4-9028-840c92d4c932
-- title:
--   $R(5,5)\le 46$
-- statement:
--   Angeltveit and McKay proved the current record upper bound $R(5,5)\le 46$: every simple graph on $46$ vertices contains a $5$-clique or a $5$-vertex independent set. The proof combines linear programming with a computer check over the remaining extremal configurations. Together with Exoo's lower bound this gives $43\le R(5,5)\le 46$.
--
--   **Formalization Note.** Stated as `Erdos77.asymmetricRamsey 5 5 ≤ 46` over the platform Ramsey-number definition.
-- source:
--   V. Angeltveit and B. D. McKay, R(5,5) ≤ 46, https://arxiv.org/abs/2409.15709 (2024; J. Graph Theory, to appear), main theorem.

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey

namespace RamseyValues

theorem ramsey_five_five_le_46 : Erdos77.asymmetricRamsey 5 5 ≤ 46 := by sorry

end RamseyValues
