-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_le_two_of_pos
-- name    : PebblingLean.Hypercube.PaperParameters.loss_le_two_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:32.770023+00:00
-- url     : https://prove2.me/theorems/cb582b8e-21b9-4368-82e6-6134a73fe3f5
-- title:
--   Paper Parameters: loss le two of pos
-- statement:
--   The Paper Parameters construction uses the loss le two of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L261-L268
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L261-L268

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

theorem PebblingLean.Hypercube.PaperParameters.loss_le_two_of_pos {n : ℕ} (hn : 0 < n) : loss n ≤ 2 := by sorry
