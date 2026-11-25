-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_contOf_subset
-- name    : PretorsionImageClosed.LinearQuiver.contOf_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:45:42.397364+00:00
-- url     : https://prove2.me/theorems/c0c0810e-31c2-4f18-8b20-a6e94c13bcca
-- title:
--   Linear Quiver: cont Of subset
-- statement:
--   The Linear Quiver construction uses the cont Of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L280-L284
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L280-L284

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

theorem PretorsionImageClosed.LinearQuiver.contOf_subset (x : CutoffPair (n + 1)) : contOf x ⊆ candRows x.restrict := by sorry
