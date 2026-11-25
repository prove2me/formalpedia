-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_cpSum_succ
-- name    : PretorsionImageClosed.LinearQuiver.cpSum_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:47:22.427971+00:00
-- url     : https://prove2.me/theorems/b6fc0909-8ef5-4c2c-99d1-bf24939d0107
-- title:
--   Linear Quiver: cp Sum succ
-- statement:
--   The Linear Quiver construction uses the cp Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L506-L512
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L506-L512

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

theorem PretorsionImageClosed.LinearQuiver.cpSum_succ (n : ℕ) :
    cpSum (n + 1) = ∑ p : CutoffPair n, C (q ^ middleCount p.1.1 p.1.2) * geomSum (p.1.1.rowsReaching + 1) := by sorry
