-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_lossProduct_nonneg
-- name    : PebblingLean.Hypercube.LossRecurrence.lossProduct_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:02.3939+00:00
-- url     : https://prove2.me/theorems/10eb86f4-788b-48cd-8388-650145be675c
-- title:
--   Loss Recurrence: loss Product nonneg
-- statement:
--   The Loss Recurrence construction uses the loss Product nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L56-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L56-L63

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

theorem PebblingLean.Hypercube.LossRecurrence.lossProduct_nonneg {next : ℕ → ℕ} {loss : ℕ → ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n) (k n : ℕ) :
    0 ≤ lossProduct next loss k n := by sorry
