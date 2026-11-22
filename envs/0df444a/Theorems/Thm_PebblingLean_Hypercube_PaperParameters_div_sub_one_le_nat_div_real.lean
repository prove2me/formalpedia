-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_div_sub_one_le_nat_div_real
-- name    : PebblingLean.Hypercube.PaperParameters.div_sub_one_le_nat_div_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:58:20.153653+00:00
-- url     : https://prove2.me/theorems/ce4403c0-3731-4889-8bc7-cf2c4701e9a8
-- title:
--   Paper Parameters: div sub one le nat div real
-- statement:
--   Lower companion to `nat_div_real_le_div`, with one unit of floor slack.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L471-L481
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L471-L481

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

theorem PebblingLean.Hypercube.PaperParameters.div_sub_one_le_nat_div_real (a d : ℕ) (hd : 0 < d) :
    (a : ℝ) / d - 1 ≤ ((a / d : ℕ) : ℝ) := by sorry
