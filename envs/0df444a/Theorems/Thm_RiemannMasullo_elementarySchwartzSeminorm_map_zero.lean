-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartzSeminorm_map_zero
-- name    : RiemannMasullo.elementarySchwartzSeminorm_map_zero
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:03:46.597605+00:00
-- url     : https://prove2.me/theorems/c0d39874-201a-4e32-be14-7b1cf002c955
-- title:
--   Weighted Schwartz bounds vanish at zero
-- statement:
--   Every iterated derivative of the zero function is zero, so every weighted supremum and its real value vanish.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L382-L384

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzSubmodule
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}

namespace RiemannMasullo

theorem elementarySchwartzSeminorm_map_zero (i : ElementarySchwartzIndex m n r) :
    (elementarySchwartzBound (0 : elementarySchwartzSubmodule m n r F).val i).toReal = 0 := by sorry

end RiemannMasullo
