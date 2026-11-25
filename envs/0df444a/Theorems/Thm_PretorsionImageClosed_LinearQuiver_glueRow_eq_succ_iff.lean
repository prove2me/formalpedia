-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_glueRow_eq_succ_iff
-- name    : PretorsionImageClosed.LinearQuiver.glueRow_eq_succ_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:42:30.609822+00:00
-- url     : https://prove2.me/theorems/96c00b4c-5fea-4a83-bae9-082a9254bddb
-- title:
--   Linear Quiver: glue Row eq succ iff
-- statement:
--   The Linear Quiver construction uses the glue Row eq succ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L153-L160
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L153-L160

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

theorem PretorsionImageClosed.LinearQuiver.glueRow_eq_succ_iff {p : CutoffPair n} {Cont : Finset (Fin (n + 1))} {a : Fin (n + 1)} :
    (glueRow p Cont).β a = n + 1 ↔ a ∈ Cont := by sorry
