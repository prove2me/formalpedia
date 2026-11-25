-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_rho_subcategory
-- name    : PretorsionImageClosed.LinearQuiver.rho_subcategory
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:28:30.884847+00:00
-- url     : https://prove2.me/theorems/f0ee6dd9-7287-4daf-8942-63ff97d73433
-- title:
--   Linear Quiver: rho subcategory
-- statement:
--   The Linear Quiver construction uses the rho subcategory property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffWeights.lean#L46-L62
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffWeights.lean#L46-L62

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffCriterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.rho_subcategory (β : RowCutoff n) :
    rho (β.subcategory (k := k)).prop = β.rowsReaching := by sorry
