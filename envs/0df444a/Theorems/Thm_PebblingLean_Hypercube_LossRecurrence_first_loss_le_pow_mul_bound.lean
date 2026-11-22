-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_first_loss_le_pow_mul_bound
-- name    : PebblingLean.Hypercube.LossRecurrence.first_loss_le_pow_mul_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:57:33.608188+00:00
-- url     : https://prove2.me/theorems/313a2458-5818-4842-ae6c-537d964f676d
-- title:
--   Loss Recurrence: first loss le pow mul bound
-- statement:
--   If every active loss is at most `q` times the next active loss, and active
--   losses are bounded by `M`, then the first loss in a path of length `k+1` is at
--   most `q^k M`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L211-L238
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L211-L238

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

theorem PebblingLean.Hypercube.LossRecurrence.first_loss_le_pow_mul_bound
    {next : ℕ → ℕ} {loss : ℕ → ℝ} {n0 : ℕ} {q M : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M)
    (k n : ℕ) (hactive : ActiveFor next n0 (k + 1) n) :
    loss n ≤ q ^ k * M := by sorry
