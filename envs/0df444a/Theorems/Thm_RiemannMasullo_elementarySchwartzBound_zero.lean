-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartzBound_zero
-- name    : RiemannMasullo.elementarySchwartzBound_zero
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T01:42:35.626582+00:00
-- url     : https://prove2.me/theorems/c1496eb3-a917-4b66-8650-ec926875e727
-- title:
--   The zeroth Schwartz bound is the global supremum
-- statement:
--   With all weights and derivative indices zero, the Schwartz bound is the supremum of the original function's norm over the whole elementary group.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L325-L327

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

namespace RiemannMasullo

theorem elementarySchwartzBound_zero (f : ElementaryLieGroup m n r F → ℂ) :
    elementarySchwartzBound f (0, 0, 0, 0) =
      ⨆ g, (‖f g‖₊ : ℝ≥0∞) := by sorry

end RiemannMasullo
