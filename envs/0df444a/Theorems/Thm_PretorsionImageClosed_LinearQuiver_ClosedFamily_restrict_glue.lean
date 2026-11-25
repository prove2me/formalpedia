-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_ClosedFamily_restrict_glue
-- name    : PretorsionImageClosed.LinearQuiver.ClosedFamily.restrict_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:14:28.823521+00:00
-- url     : https://prove2.me/theorems/faf0b9a7-f0f9-492e-a617-6c0c7693c2f4
-- title:
--   Closed Family: restrict glue
-- statement:
--   The Closed Family construction uses the restrict glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L242-L244
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L242-L244

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

theorem PretorsionImageClosed.LinearQuiver.ClosedFamily.restrict_glue (D : ClosedFamily n) (J : Finset (Fin (n + 1))) (hJ : J ⊆ adm D.1) :
    (D.glue J hJ).restrict = D := by sorry
