-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_lastCount_glue
-- name    : PretorsionImageClosed.LinearQuiver.lastCount_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:17:16.819688+00:00
-- url     : https://prove2.me/theorems/a133a369-5cd6-463f-a6b0-8bd1bdf8dc18
-- title:
--   Linear Quiver: last Count glue
-- statement:
--   The Linear Quiver construction uses the last Count glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L276-L281
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L276-L281

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.lastCount_glue (D : IntervalFamily n) (J : Finset (Fin (n + 1))) :
    (D.glue J).lastCount = J.card := by sorry
