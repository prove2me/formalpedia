-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_one_twentieth_le_stackMargin
-- name    : PebblingLean.Hypercube.PaperParameters.one_twentieth_le_stackMargin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:56.53973+00:00
-- url     : https://prove2.me/theorems/c27cb03a-893b-49e8-94b4-051d9fce40ff
-- title:
--   Paper Parameters: one twentieth le stack Margin
-- statement:
--   A convenient certified lower bound for the stack margin.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1204-L1219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1204-L1219

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

theorem PebblingLean.Hypercube.PaperParameters.one_twentieth_le_stackMargin : (1 : ℝ) / 20 ≤ stackMargin := by sorry
