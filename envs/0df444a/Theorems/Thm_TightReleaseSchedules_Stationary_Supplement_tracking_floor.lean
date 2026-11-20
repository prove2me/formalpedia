-- Prove2me | Theorems.Thm_TightReleaseSchedules_Stationary_Supplement_tracking_floor
-- name    : TightReleaseSchedules.Stationary.Supplement.tracking_floor
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T04:22:08.948253+00:00
-- url     : https://prove2.me/theorems/fa58f383-e36a-429c-be78-553de541e04e
-- title:
--   Lemma 5.2 — tracking floor 2^{-13}Tϕ with any number of releases
-- statement:
--   Let $T\ge8$ and $d\ge1$ be integers, let $\theta_0\in\mathbb R^d$, and let $\eta\ge0$ satisfy $\eta T\le\tfrac14$ and $d\eta\le\tfrac18$. Put $\phi=\min\{(d\eta)^{2/3},\eta^2T^2\}$ as in Theorem 5.1. Consider the paths that start exactly at the pretrained vector and drift by at most $\eta$ per step:
--
--   $$
--   \theta_1=\theta_0,\qquad \|\theta_t-\theta_{t-1}\|_2\le\eta\quad(2\le t\le T).
--   $$
--
--   Take any number $B$ of release slots, any random seed, and any randomized causal policy. Its worst-case cumulative half-squared risk over these paths satisfies
--
--   $$
--   \sup_{\theta_{1:T}}\ \frac12\,\mathbb E\sum_{t=1}^{T}\|w_t-\theta_t\|_2^2\ \ge\ 2^{-13}\,T\phi .
--   $$
--
--   This is the tracking cost that remains even when a release is allowed after every observation. Theorem 5.1's lower bound combines it with the release-program bound.
--
--   **Formalization Note** The path class is the drift class $\mathcal P(0,\eta)$: $\|\theta_1-\theta_0\|_2\le0$ is $\theta_1=\theta_0$. "Any number of releases" is the quantifier over every $B$; with $B\ge T$ a release after every round is possible.
--
--   Differences from the source:
--   - encoding: rounds $t=1,\dots,T$, randomized causal policies with at most $B$ releases and expected half-squared risk → index $i$ of `Fin T` is round $i+1$, the base mission's `ReleasePolicy`/`IsCausal` on an arbitrary seed space, `ENNReal`-valued `policyRisk` compared with `ENNReal.ofReal` of the real bound; reason: the base mission's conventions, which change no instance and exclude no competitor with infinite risk.
--   - reading: "every policy, with any number of releases" → every $B\in\mathbb N$ and every causal randomized policy with $B$ release slots on every seed space; reason: every policy releases finitely often within the horizon, and a policy releasing after every round has $B=T$ slots.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), Lemma 5.2, printed p.17, PDF p.18; ϕ from Theorem 5.1, printed p.15, PDF p.16

import Definitions.Def_TightReleaseSchedules_Stationary_Supplement_drift_class

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace TightReleaseSchedules.Stationary.Supplement

open TightReleaseSchedules.Stationary

/-- Lemma 5.2 (printed p. 17, PDF p. 18), tracking floor: every causal policy, with any
number `B` of release slots and any seed, has worst-case risk at least `2^{-13}Tϕ` over the
paths with `θ₁ = θ₀` and increments of norm at most `η` (the class `P(0, η)`). -/
theorem tracking_floor (T d : ℕ) (hT : 8 ≤ T) (hd : 0 < d) (η : ℝ) (hη : 0 ≤ η)
    (hηT : η * T ≤ 1 / 4) (hdη : (d : ℝ) * η ≤ 1 / 8) (θ₀ : Vector d) :
    ∀ (B : ℕ) (s : RandomSeed) (π : ReleasePolicy s T d B), IsCausal π →
      ENNReal.ofReal ((2 : ℝ) ^ (-13 : ℤ) * T * trackingRate T d η) ≤
        driftWorstRisk θ₀ 0 η π := by sorry

end TightReleaseSchedules.Stationary.Supplement
