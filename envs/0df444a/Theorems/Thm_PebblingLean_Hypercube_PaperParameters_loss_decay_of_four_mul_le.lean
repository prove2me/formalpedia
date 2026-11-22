-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_decay_of_four_mul_le
-- name    : PebblingLean.Hypercube.PaperParameters.loss_decay_of_four_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:55.662586+00:00
-- url     : https://prove2.me/theorems/46423a9f-ebff-4869-afac-57b66b4d2eb7
-- title:
--   Paper Parameters: loss decay of four mul le
-- statement:
--   If the next recursive dimension is at most one quarter of the current
--   dimension, then the loss drops geometrically.  We use the relaxed ratio `1/2`;
--   the proof gives much more.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L297-L312
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L297-L312

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

theorem PebblingLean.Hypercube.PaperParameters.loss_decay_of_four_mul_le {m n : ℕ}
    (hm : 0 < m) (hmn : 4 * m ≤ n) :
    loss n ≤ ((1 : ℝ) / 2) * loss m := by sorry
