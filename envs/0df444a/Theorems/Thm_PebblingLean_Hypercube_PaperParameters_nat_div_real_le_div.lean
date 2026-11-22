-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_nat_div_real_le_div
-- name    : PebblingLean.Hypercube.PaperParameters.nat_div_real_le_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:06.651527+00:00
-- url     : https://prove2.me/theorems/8f802e40-795f-4805-9554-0512733db873
-- title:
--   Paper Parameters: nat div real le div
-- statement:
--   The Paper Parameters construction uses the nat div real le div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L460-L468
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L460-L468

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

theorem PebblingLean.Hypercube.PaperParameters.nat_div_real_le_div (a d : ℕ) (hd : 0 < d) :
    ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := by sorry
