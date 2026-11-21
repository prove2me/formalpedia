-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartzSeminorm_neg
-- name    : RiemannMasullo.elementarySchwartzSeminorm_neg
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:03:42.50851+00:00
-- url     : https://prove2.me/theorems/372bb311-c640-45e2-9dba-52681951105b
-- title:
--   Weighted Schwartz bounds are invariant under negation
-- statement:
--   Absolute homogeneity at the scalar minus one gives invariance under negation.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L403-L406

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzSubmodule
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}

namespace RiemannMasullo

theorem elementarySchwartzSeminorm_neg (i : ElementarySchwartzIndex m n r)
    (f : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (-f).val i).toReal =
      (elementarySchwartzBound f.val i).toReal := by sorry

end RiemannMasullo
