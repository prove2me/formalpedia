-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_colValue_colOf
-- name    : PretorsionImageClosed.LinearQuiver.colValue_colOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:46:22.314235+00:00
-- url     : https://prove2.me/theorems/8d59297a-95d2-4db4-8750-0f24bf596156
-- title:
--   Linear Quiver: col Value col Of
-- statement:
--   The Linear Quiver construction uses the col Value col Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L261-L266
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L261-L266

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

theorem PretorsionImageClosed.LinearQuiver.colValue_colOf (x : CutoffPair (n + 1)) : colValue (colOf x) = x.1.2.α (Fin.last n) := by sorry
