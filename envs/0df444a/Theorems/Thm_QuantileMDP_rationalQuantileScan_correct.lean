-- Prove2me | Theorems.Thm_QuantileMDP_rationalQuantileScan_correct
-- name    : QuantileMDP.rationalQuantileScan_correct
-- status  : Proved
-- author  : @shuffle
-- created : 2026-11-14T03:02:05.507208+00:00
-- url     : https://prove2.me/theorems/364f57e4-e531-4b7a-b239-939b3e6207e9
-- title:
--   Quantile MDP — correctness of an executable rational threshold scan
-- statement:
--   For a finite-state, finite-action MDP with bounded integer rewards and rational transition probabilities, an executable integer-threshold scan computes exactly the finite-horizon optimal lower quantile at every rational level in [0,1]. For a positive level it selects the least threshold whose minimum closed lower-tail probability reaches the level. At level zero it selects the greatest threshold whose minimum open lower-tail probability is zero. The scan uses finite action minima and rational arithmetic. It is an alternative to the breakpoint implementation in §4 of Li, Zhong and Brandeau and makes no claim about that implementation's running time.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §4, pp. 16–19. https://arxiv.org/abs/1711.05788v5

import Definitions.Def_QuantileMDP_dpValue
import Definitions.Def_QuantileMDP_rationalQuantileScan

open QuantileMDP
open scoped ENNReal

theorem QuantileMDP.rationalQuantileScan_correct {S A : Type*} [Fintype S] (M : Model S A) [Fintype A]
    (actions : ℕ → S → Finset A) (hne : ∀ t s, (actions t s).Nonempty)
    (ha : ∀ t s a, a ∈ actions t s ↔ a ∈ M.adm t s)
    (p : ℕ → S → A → S → ℚ) (hp : ∀ t s a i, 0 ≤ p t s a i)
    (hprob : ∀ t s a i, ENNReal.ofReal (p t s a i : ℝ) = M.P t s a i)
    (r : ℕ → S → A → S → ℤ) (hr : ∀ t s a i, M.r t s a i = (r t s a i : ℝ))
    (R : ℕ) (hR : ∀ t s a i, |r t s a i| ≤ (R : ℤ))
    (T : ℕ) (s : S) (τ : ℚ) (hτ : (τ : ℝ) ∈ Set.Icc 0 1) :
    ∃ z : ℤ, rationalQuantileScan actions hne p r R T s τ = some z ∧
      dpValue M T 0 s (τ : ℝ) = ((z : ℝ) : EReal) := by sorry
