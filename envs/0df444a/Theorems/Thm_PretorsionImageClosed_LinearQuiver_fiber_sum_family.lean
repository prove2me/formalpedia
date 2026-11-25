-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_fiber_sum_family
-- name    : PretorsionImageClosed.LinearQuiver.fiber_sum_family
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:10:02.201232+00:00
-- url     : https://prove2.me/theorems/5f41d019-d384-4e89-91cc-58b40ee7ad25
-- title:
--   Linear Quiver: fiber sum family
-- statement:
--   The Linear Quiver construction uses the fiber sum family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L372-L404
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L372-L404

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

theorem PretorsionImageClosed.LinearQuiver.fiber_sum_family (D : ClosedFamily n) (f : ClosedFamily (n + 1) → Rq[X])
    (g : Finset (Fin (n + 1)) → Rq[X]) (hfg : ∀ J (hJ : J ⊆ adm D.1), f (D.glue J hJ) = g J) :
    ∑ D' ∈ univ.filter (fun D' : ClosedFamily (n + 1) => D'.restrict = D), f D' =
      ∑ J ∈ (adm D.1).powerset, g J := by sorry
