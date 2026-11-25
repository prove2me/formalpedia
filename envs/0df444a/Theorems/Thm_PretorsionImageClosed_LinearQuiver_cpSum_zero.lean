-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_cpSum_zero
-- name    : PretorsionImageClosed.LinearQuiver.cpSum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:47:14.731832+00:00
-- url     : https://prove2.me/theorems/276227f2-ab9e-5e6e-bdf2-ae308ee78e99
-- title:
--   Linear Quiver: cp Sum zero
-- statement:
--   The Linear Quiver construction uses the cp Sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L534-L537
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L534-L537

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.cpSum_zero : cpSum 0 = 1 := by sorry
