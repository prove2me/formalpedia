-- Prove2me | Theorems.Thm_QuantileMDP_theorem_4_counterexample
-- name    : QuantileMDP.theorem_4_counterexample
-- status  : Proved
-- author  : @shuffle
-- created : 2026-11-14T02:44:20.461347+00:00
-- url     : https://prove2.me/theorems/b92486c4-e5ee-41fe-9818-a89e3646ecc8
-- title:
--   Quantile MDP Theorem 4 — a counterexample to the CVaR weighting rule
-- statement:
--   The weighted CVaR evaluation in Theorem 4 can depend on the selection of an optimizer for the quantile allocation, even with one state, one action, one step, and a reward identically equal to one. At quantile level 1/2, the allocation q = 0 is feasible and attains the quantile OPT value under the corrected budget (it also optimizes the printed weak-budget problem). The true upper-tail CVaR is 1. The weighted formula evaluated at q = 0 gives 2.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.1, Theorem 4, p. 21. https://arxiv.org/abs/1711.05788v5

import Definitions.Def_QuantileMDP_upperCVaR
import Definitions.Def_QuantileMDP_opt

open QuantileMDP

theorem QuantileMDP.theorem_4_counterexample :
    let p : Unit → ℝ := fun _ => 1
    let g : Unit → ℝ → EReal := fun _ _ => 1
    let q : Unit → ℝ := fun _ => 0
    q ∈ Feasible p (1 / 2) ∧
      (⨅ i, ⨅ (_ : q i ≠ 1), g i (q i)) = opt p g (1 / 2) ∧
      upperCVaR (MeasureTheory.Measure.dirac (1 : ℝ)) (1 / 2) <
        (∑ i, p i * (1 - q i) * (1 : ℝ)) / (1 - 1 / 2) := by sorry
