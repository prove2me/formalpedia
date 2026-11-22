-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_real_le_n
-- name    : PebblingLean.Hypercube.PaperParameters.splitA_real_le_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:45.969751+00:00
-- url     : https://prove2.me/theorems/f890f1ff-7721-4554-adf4-61523f63131a
-- title:
--   Paper Parameters: split A real le n
-- statement:
--   The Paper Parameters construction uses the split A real le n property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L453-L458
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L453-L458

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

theorem PebblingLean.Hypercube.PaperParameters.splitA_real_le_n {K : ℝ} {n : ℕ} :
    (splitA K n : ℝ) ≤ (n : ℝ) := by sorry
