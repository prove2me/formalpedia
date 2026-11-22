-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_nonneg
-- name    : PebblingLean.Hypercube.PaperParameters.loss_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:30.773804+00:00
-- url     : https://prove2.me/theorems/1415ff16-5180-47ad-88c2-e22a0c1c3fb1
-- title:
--   Paper Parameters: loss nonneg
-- statement:
--   The Paper Parameters construction uses the loss nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L253-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L253-L255

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

theorem PebblingLean.Hypercube.PaperParameters.loss_nonneg (n : ℕ) : 0 ≤ loss n := by sorry
