-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_leastRealization_middle
-- name    : PretorsionImageClosed.Statement.leastRealization_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:48:55.383974+00:00
-- url     : https://prove2.me/theorems/be18dc19-c83a-45c0-b3a4-d1bcfd211295
-- title:
--   Statement: least Realization middle
-- statement:
--   The Statement construction uses the least Realization middle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean#L60-L63
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean#L60-L63

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)

theorem PretorsionImageClosed.Statement.leastRealization_middle : (leastRealization Z hZ).middle = Z.prop := by sorry
