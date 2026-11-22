-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_le_of_le
-- name    : PebblingLean.Hypercube.PaperParameters.loss_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:54.686257+00:00
-- url     : https://prove2.me/theorems/a5c7080f-4f33-4851-82b8-052c9a7aa506
-- title:
--   Paper Parameters: loss le of le
-- statement:
--   The Paper Parameters construction uses the loss le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L283-L292
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L283-L292

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters

theorem PebblingLean.Hypercube.PaperParameters.loss_le_of_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    loss n ≤ loss m := by sorry
