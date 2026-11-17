-- Prove2me | Theorems.Thm_RGMISFast_root_count_expectation_drift
-- name    : RGMISFast.root_count_expectation_drift
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-16T00:02:25.370382+00:00
-- url     : https://prove2.me/theorems/0616f247-b6e3-4a73-bdb1-fee717e78e36
-- title:
--   Expected active root-connected counts satisfy nonlinear decay
-- statement:
--   For a finite graph and a fixed root under independent unit-rate exponential ranks, fix $k\ge1$ and $t>0$. On $0\le s\le t$, the finite expectation
--   $$f(s)=\mathbb E[Y_k(s)]$$
--   is nonnegative and continuous, and differentiable in the interior, with
--   $$f'(s)\le-\frac{k}{e}f(s)^{1+1/k}.$$
--   The formal statement identifies the lower integral with $\operatorname{ofReal}(f(s))$ throughout the closed interval, making finiteness explicit.
--
--   This auxiliary result uses the unconditional version of the decay inequality in the proof of Lemma 5.2. The paper presents its argument after fixing a root rank above the time horizon. For the unconditional process, arrivals at the root only add losses to the count; the non-root arrival contribution gives the same upper bound for the derivative. Thus this formulation retains the paper's coefficient while incorporating root-rank averaging into the stochastic step. It does not assert the final integrated bound $f(t)\le(e/t)^k$.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, §5.1, proof of Lemma 5.2, printed pp.18–20 (PDF pp.20–22), short-window arrival calculation (20), Lemma 5.1 and Jensen leading to (21). Auxiliary unconditional variant: root arrivals contribute additional losses, which are discarded in the upper bound on the derivative.

import Mathlib
import Definitions.Def_RGMISFast_Y
import Definitions.Def_RGMISFast_rankLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RGMISFast

theorem RGMISFast.root_count_expectation_drift {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (t : ℝ) (ht : 0 < t)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ f f' : ℝ → ℝ,
      (∀ s ∈ Set.Icc 0 t,
        (∫⁻ r, (Y G u k s r : ℝ≥0∞) ∂(rankLaw V)) = ENNReal.ofReal (f s)) ∧
      ContinuousOn f (Set.Icc 0 t) ∧
      (∀ s ∈ Set.Icc 0 t, 0 ≤ f s) ∧
      (∀ s ∈ Set.Ioo 0 t, HasDerivAt f (f' s) s) ∧
      (∀ s ∈ Set.Ioo 0 t,
        f' s ≤ -(k:ℝ) / Real.exp 1 * f s ^ (1+(k:ℝ)⁻¹)) := by sorry
