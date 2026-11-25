-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_finsum_pretorsionWeight
-- name    : PretorsionImageClosed.LinearQuiver.finsum_pretorsionWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:21:23.516357+00:00
-- url     : https://prove2.me/theorems/fca89ba6-7ba1-4e2d-bf60-c193558c85f4
-- title:
--   Linear Quiver: finsum pretorsion Weight
-- statement:
--   The Linear Quiver construction uses the finsum pretorsion Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffWeights.lean#L96-L100
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffWeights.lean#L96-L100

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

theorem PretorsionImageClosed.LinearQuiver.finsum_pretorsionWeight :
    ∑ᶠ P : PretorsionTheory (Statement.LinRep k n), pretorsionWeight k n P =
      ∑ p : CutoffPair n, cpWeight p := by sorry
