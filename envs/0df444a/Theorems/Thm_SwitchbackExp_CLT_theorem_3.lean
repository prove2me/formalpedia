-- Prove2me | Theorems.Thm_SwitchbackExp_CLT_theorem_3
-- name    : SwitchbackExp.CLT.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:11.36939+00:00
-- url     : https://prove2.me/theorems/5e5222b1-4a10-49ce-8bd9-180e4f333559
-- title:
--   Theorem 3, p. 17 — under 𝕋* with fair coins and Assumptions 1–4, (τ̂_m − τ_m)/√Var(τ̂_m) → 𝒩(0, 1) as n → ∞
-- statement:
--   Fix the carryover order $m\ge1$. For each $n$ consider the $n$-replica experiment with $T=nm$ periods, potential outcomes $Y^{(n)}$, and the optimal design of Theorem 2, whose randomization points are
--   $$\mathbb T^*=\{1,2m+1,3m+1,\dots,(n-2)m+1\},$$
--   each with a fair coin. Assume that
--
--   1. every $Y^{(n)}$ is non-anticipating (Assumption 1) and has $m$-carryover effects (Assumption 2);
--   2. the potential outcomes are bounded uniformly in $n$: there is $B>0$ with $|Y^{(n)}_t(w)|\le B$ for all $n$, all $t\in[T]$ and all paths (Assumption 3);
--   3. the variance is non-negligible (Assumption 4): there is $c>0$ with $\mathrm{Var}(\hat\tau_m)\ge c/n$ for all large $n$.
--
--   Then, as $n\to\infty$,
--   $$\frac{\hat\tau_m-\tau_m}{\sqrt{\mathrm{Var}(\hat\tau_m)}}\xrightarrow{D}\mathcal N(0,1),$$
--   where $\hat\tau_m$ is the Horvitz–Thompson estimator, $\tau_m$ the lag-$m$ causal effect and $\mathrm{Var}(\hat\tau_m)$ the randomization variance of $\hat\tau_m$ in the $n$-th experiment.
--
--   This finite-population central limit theorem justifies normal-approximation tests and confidence intervals for the lag-$m$ effect from a single switchback experiment; it does not require $\mathrm{Var}(\hat\tau_m)$ to converge.
--
--   **Formalization Note** The page lists Assumptions 1–2 and 4 only. Assumption 3 with one bound $B$ for all $n$ is added: the proof (p. ec27) uses it in every condition of Lemma EC.1, the text before the theorem invokes it, and without it the statement is false (outcomes of order $n$ in a single block dominate the variance and the limit is a two- or three-point law). The randomness is the uniform distribution on the coin vectors of $\mathbb T^*$, whose image under the path map is the design's law; the estimator, estimand and variance are the model's `htEstimator`, `tau` and `htVar`. Rows $n<4$ are degenerate but irrelevant to the limit; Assumption 4 makes the variance positive for all large $n$, so the division by $\sqrt{\mathrm{Var}}$ is meaningful in the limit.
-- source:
--   arXiv:2009.00148v4, Theorem 3, p. 17; proof EC.4.4, pp. ec27–ec28

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_CLT_Setting

open MeasureTheory ProbabilityTheory Filter

open SwitchbackExp.Design

namespace SwitchbackExp.CLT

/-- Theorem 3 (Asymptotic Normality), p. 17: for fixed `m`, in the `n`-replica experiment with
`T = n m` periods under the optimal design `𝕋* = {1, 2m+1, …, (n−2)m+1}` with fair coins, Assumptions 1–2,
Assumption 3 with one bound `B` for all `n` (added, see the natural-language statement), and
Assumption 4, `(τ̂_m − τ_m)/√Var(τ̂_m) → 𝒩(0, 1)` in distribution as `n → ∞`. -/
theorem theorem_3 (m : ℕ) (hm : 1 ≤ m) (Y : ℕ → Outcomes)
    (hA1 : ∀ n, NonAnticipating (n * m) (Y n)) (hA2 : ∀ n, Carryover m (n * m) (Y n))
    (hA3 : ∃ B > 0, ∀ n, Bounded B (n * m) (Y n)) (hA4 : NonNegligibleVariance m Y) :
    TendstoInDistribution
      (fun n (c : Coins m n) =>
        (htEstimator m (n * m) (optPoints m n) half (Y n) (pathOf (optPoints m n) c) - tau m (n * m) (Y n)) /
          Real.sqrt (htVar m (n * m) (optPoints m n) half (Y n)))
      atTop id (fun n => coinMeasure m n) (gaussianReal 0 1) := by sorry

end SwitchbackExp.CLT
