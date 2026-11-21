-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartzSeminorm_zero
-- name    : RiemannMasullo.elementarySchwartzSeminorm_zero
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:17:18.340153+00:00
-- url     : https://prove2.me/theorems/a5dd6aad-2954-4cfb-8c10-aad738f66be1
-- title:
--   The zeroth elementary Schwartz seminorm equals the uniform norm
-- statement:
--   The seminorm with all indices zero is the supremum of the function's absolute value on the entire elementary group.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L430-L431

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

namespace RiemannMasullo

theorem elementarySchwartzSeminorm_zero (f : ElementarySchwartz m n r F) :
    elementarySchwartzSeminorm (0, 0, 0, 0) f = ⨆ g, ‖f g‖ := by sorry

end RiemannMasullo
