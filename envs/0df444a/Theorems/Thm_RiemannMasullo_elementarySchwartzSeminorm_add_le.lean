-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartzSeminorm_add_le
-- name    : RiemannMasullo.elementarySchwartzSeminorm_add_le
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:03:40.756571+00:00
-- url     : https://prove2.me/theorems/f8a958f8-5ed4-4a08-b4c5-450169734996
-- title:
--   Subadditivity of the weighted Schwartz bounds
-- statement:
--   Linearity of mixed derivatives and the triangle inequality give the pointwise estimate. Taking suprema and using finiteness gives the real inequality.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L388-L392

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzSubmodule
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}

namespace RiemannMasullo

theorem elementarySchwartzSeminorm_add_le (i : ElementarySchwartzIndex m n r)
    (f g : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (f + g).val i).toReal ≤
      (elementarySchwartzBound f.val i).toReal + (elementarySchwartzBound g.val i).toReal := by sorry

end RiemannMasullo
