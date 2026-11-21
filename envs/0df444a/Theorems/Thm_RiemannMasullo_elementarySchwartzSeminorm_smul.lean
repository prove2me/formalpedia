-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartzSeminorm_smul
-- name    : RiemannMasullo.elementarySchwartzSeminorm_smul
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:03:42.551597+00:00
-- url     : https://prove2.me/theorems/e3f591ae-1551-49c8-b8bc-420a69757036
-- title:
--   Absolute homogeneity of every weighted Schwartz bound
-- statement:
--   Mixed derivatives scale by the scalar on each Euclidean fibre. Its norm can therefore be factored out of the supremum.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L396-L399

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzSubmodule
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}

namespace RiemannMasullo

theorem elementarySchwartzSeminorm_smul (i : ElementarySchwartzIndex m n r)
    (c : ℂ) (f : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (c • f).val i).toReal =
      ‖c‖ * (elementarySchwartzBound f.val i).toReal := by sorry

end RiemannMasullo
