-- Prove2me | Theorems.Thm_TightContinualCounting_LowerBounds_lemma_11
-- name    : TightContinualCounting.LowerBounds.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:54.59207+00:00
-- url     : https://prove2.me/theorems/8e2543c8-a261-4b8d-8fef-00e644f3fdb3
-- title:
--   Lemma 11 — pointwise accuracy lower bound for both probes
-- statement:
--   Let $n,H,k\ge1$, $m=4^H$ and $q=km\le n$. Fix any binary vector $x\in\{0,1\}^m$, any real vector $W\in\mathbb R^n$ and $a>1$. For uniform $J\in[m]$ set $Y_J=(W-A_nE_k(x\oplus e_J))_{[q]}/k$. Write $R=\|W-A_nE_k(x)\|_\infty$ and $Q=q^{-1}\sum_{t\in[q]}(W-A_nE_k(x))_t^2$. Then both bounds hold:
--
--   $$
--   \Pr_J[S_{\rm mid}(J,Y_J)\ge H/4]\ge1-\frac{4a}{\sqrt H}-\frac{4R}{kH(a-1)},
--   $$
--   $$
--   \Pr_J[S_{\rm mean}(J,Y_J)\ge H/4]\ge1-\frac{4a}{\sqrt H}-\frac{8Q}{k^2H(a-1)^2}.
--   $$
--
--   Only $J$ is random in these pointwise inequalities. They require no privacy assumption and apply to each output of every mechanism, including laws without atoms. The two constants are exactly those in the source statement.
--
--   Differences from the source:
--   - encoding: coordinates [d]={1,…,d} → coordinates Fin d={0,…,d−1}; reason: the order-preserving reindexing preserves every interval, vector and finite sum
--   - generalization: fixed X,W=M(E_k(X)) → every binary x and every real output vector W; reason: the proof fixes arbitrary x,W and uses only their unshifted error, so this includes every source mechanism realization without conditioning on zero-mass singleton events
--   - encoding: probability at least a possibly negative real bound → ENNReal.ofReal of that bound is at most the uniform event mass; reason: a probability is nonnegative, so truncating a negative lower bound to zero is equivalent
-- source:
--   Charlie Harrison, Ethan Leeman, Tight Lower Bounds for Differentially Private Continual Counting, STOC 2027 submission #1453 (October 2026), Lemma 11 p.10; proof pp.10–13

import Mathlib
import Definitions.Def_TightContinualCounting_LowerBounds_sampling

open MeasureTheory
open scoped ENNReal

namespace TightContinualCounting.LowerBounds

/-- Lemma 11, p.10, pointwise for every real output W (as its proof on pp.10–13). -/
theorem lemma_11 (n H k : ℕ) (hn : 1 ≤ n) (hH : 1 ≤ H) (hk : 1 ≤ k)
    (hq : k * 4 ^ H ≤ n) (a : ℝ) (ha : 1 < a)
    (x : Fin (4 ^ H) → Bool) (W : Fin n → ℝ) :
    ENNReal.ofReal (1 - 4 * a / Real.sqrt H -
        4 * residualMax k x W / ((k : ℝ) * H * (a - 1))) ≤
      uniformFinite (Fin (4 ^ H))
        {j | (H : ℝ) / 4 ≤ score H k a .mid j (shiftedResidual H k hq x W j)} ∧
    ENNReal.ofReal (1 - 4 * a / Real.sqrt H -
        8 * residualMeanSquare H k hq x W / ((k : ℝ) ^ 2 * H * (a - 1) ^ 2)) ≤
      uniformFinite (Fin (4 ^ H))
        {j | (H : ℝ) / 4 ≤ score H k a .mean j (shiftedResidual H k hq x W j)} := by sorry

end TightContinualCounting.LowerBounds
