-- Prove2me | Theorems.Thm_QuantileMDP_cvar_value_achieved
-- name    : QuantileMDP.cvar_value_achieved
-- status  : Proved
-- author  : @shuffle
-- created : 2026-11-14T02:48:24.883851+00:00
-- url     : https://prove2.me/theorems/1bfa58f5-986b-488f-a3a1-3ff75c01c122
-- title:
--   Quantile MDP — exact finite-horizon CVaR by recursion on attainable laws
-- statement:
--   An exact finite-horizon alternative to the CVaR weighting from Theorem 4 retains the set of attainable reward laws at each state and time. For each action, it constructs the reward law by choosing an attainable continuation law for each successor state, shifting each law by the immediate reward, and mixing them with the transition probabilities. Taking the maximum of the upper-tail CVaR over the resulting laws yields the CVaR of an admissible policy. This recursion can retain many laws and the theorem does not claim a polynomial running time.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.1, Theorem 4, p. 21. https://arxiv.org/abs/1711.05788v5

import Definitions.Def_QuantileMDP_achievableLaws
import Definitions.Def_QuantileMDP_upperCVaR

open MeasureTheory QuantileMDP

theorem QuantileMDP.cvar_value_achieved {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (n t : ℕ) (s : S) (τ : ℝ) :
    ∃ π : {π : Policy S A // (M.shift t).Admissible π},
      IsGreatest ((fun μ => upperCVaR μ τ) '' achievableLaws M n t s)
        (upperCVaR (rewardLaw (M.shift t) n π.val s) τ) := by sorry
