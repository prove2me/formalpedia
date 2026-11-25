-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_contOf_glue
-- name    : PretorsionImageClosed.LinearQuiver.contOf_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:46:08.432577+00:00
-- url     : https://prove2.me/theorems/b82f72d8-41aa-4cfb-bd02-6dafd8826d40
-- title:
--   Linear Quiver: cont Of glue
-- statement:
--   The Linear Quiver construction uses the cont Of glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L327-L331
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L327-L331

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

theorem PretorsionImageClosed.LinearQuiver.contOf_glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hc : Allowed p Cont c) : contOf (glue p Cont c hc) = Cont := by sorry
