-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_le_greatestRealization
-- name    : PretorsionImageClosed.Statement.le_greatestRealization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:07:25.759471+00:00
-- url     : https://prove2.me/theorems/7838e564-ac85-425a-9c01-ef783ca822b2
-- title:
--   Statement: le greatest Realization
-- statement:
--   **Corollary 4.5.** `(T⁺(Z), F⁻(Z))` is the greatest pretorsion theory with
--   intersection `Z`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L268-L269
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L268-L269

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
open Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)
variable {Z hZ}
variable (hZ : Z.IsImageClosed) (P : PretorsionTheory C) (hP : P.middle = Z.prop)
include hP

theorem PretorsionImageClosed.Statement.le_greatestRealization : P.LE (greatestRealization Z hZ) := by sorry
