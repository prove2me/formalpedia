-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_geomSum_le_two_of_le_half
-- name    : PebblingLean.Hypercube.LossRecurrence.geomSum_le_two_of_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:57:30.725838+00:00
-- url     : https://prove2.me/theorems/ab32e476-5fc4-4f58-874b-e93a96d994ff
-- title:
--   Loss Recurrence: geom Sum le two of le half
-- statement:
--   The Loss Recurrence construction uses the geom Sum le two of le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L196-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L196-L206

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.LossRecurrence

theorem PebblingLean.Hypercube.LossRecurrence.geomSum_le_two_of_le_half {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_half : q ≤ (1 : ℝ) / 2) (k : ℕ) :
    geomSum q k ≤ 2 := by sorry
