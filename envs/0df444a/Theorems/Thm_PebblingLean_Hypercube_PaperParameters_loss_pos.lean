-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_pos
-- name    : PebblingLean.Hypercube.PaperParameters.loss_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:58:07.920923+00:00
-- url     : https://prove2.me/theorems/f26f5a87-96d4-4f60-9e4f-36e553e80387
-- title:
--   Paper Parameters: loss pos
-- statement:
--   The Paper Parameters construction uses the loss pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L257-L259
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L257-L259

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

theorem PebblingLean.Hypercube.PaperParameters.loss_pos {n : ℕ} (hn : 0 < n) : 0 < loss n := by sorry
