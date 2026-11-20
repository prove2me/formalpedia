-- Prove2me | Theorems.Thm_TightReleaseSchedules_Stationary_Supplement_gradual_drift_release_schedules
-- name    : TightReleaseSchedules.Stationary.Supplement.gradual_drift_release_schedules
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T04:21:41.057331+00:00
-- url     : https://prove2.me/theorems/8aa0088f-365c-4d82-a0ce-f9ba9d788594
-- title:
--   Theorem 5.1 — release schedules under gradual drift, R*_T between 2^{-35}(F*_B+Tϕ) and 12F*_B+50Tϕ
-- statement:
--   Let $B\ge0$, $T\ge8$ and $d\ge1$ be integers, and let $\theta_0\in\mathbb R^d$ be the pretrained vector. Let the shift and drift parameters satisfy
--
--   $$
--   0<\Delta\le\tfrac12,\qquad \eta\ge0,\qquad \eta T\le\tfrac14,\qquad d\eta\le\tfrac18 ,
--   $$
--
--   and put $\phi=\min\{(d\eta)^{2/3},\eta^2T^2\}$. Write $F^*_B$ for the minimum over integer schedules of the program $F(\tau)=\sum_{j=0}^{B}(L_jd/x_j+\eta^2L_j^3)$, where $x_0=d/\Delta^2$ and $x_j=\max\{\tau_j,d/\Delta^2\}$ for $j\ge1$. Let $R^*_T(B;\Delta,\eta)$ be the minimax cumulative half-squared risk over the drift class $\mathcal P(\Delta,\eta)$. Then:
--
--   1. $$R^*_T(B;\Delta,\eta)\le12F^*_B+50T\phi .$$
--   2. The bound is attained by a deterministic release schedule. For every schedule $\tau$ with $F(\tau)=F^*_B$, Algorithm 2 on $\tau$ is causal and has fixed release dates. At a release after $n\ge1$ labels it averages the most recent $\min\{n,\lceil(d/\eta^2)^{1/3}\rceil\}$ anchored cross-moments (all $n$ labels when $\eta=0$) and projects onto the ball of radius $\Delta+\eta n$. Its worst-case risk over $\mathcal P(\Delta,\eta)$ is at most $12F^*_B+50T\phi$.
--   3. If additionally $d\ge2+\log_2\max\{1,B\log_2T\}$, then, over all randomized policies with at most $B$ releases and adaptively chosen release times,
--
--   $$
--   R^*_T(B;\Delta,\eta)\ \ge\ 2^{-35}\big(F^*_B+T\phi\big).
--   $$
--
--   The upper bound holds without the dimension condition. In the stated regime, deterministic schedules therefore attain the minimax rate up to absolute constants. The program $F$ charges estimation error and staleness, and $T\phi$ is the tracking cost that remains even with unrestricted releases (Lemma 5.2).
--
--   **Formalization Note** Round $t$ is index $t-1$ of `Fin T`. Risks are extended nonnegative reals compared with `ENNReal.ofReal` of the real bounds. The minimax value is the set infimum over every seed space and every causal policy with $B$ release slots. The standing assumption $\Delta+\eta T\le1$ of §3.2 follows from the hypotheses.
--
--   Differences from the source:
--   - encoding: rounds $t=1,\dots,T$, randomized causal policies with at most $B$ releases, expected half-squared risk and $\inf_\pi\sup_\theta$ → index $i$ of `Fin T` is round $i+1$, the base mission's `ReleasePolicy`/`IsCausal` on an arbitrary seed space, `ENNReal`-valued `policyRisk` compared with `ENNReal.ofReal` of the real bound, and the minimax value as a set infimum over all seed spaces and causal policies; reason: the base mission's conventions, which change no instance and exclude no competitor with infinite risk.
--   - encoding: $F^*_B=\min_\tau F(\tau)$ → the real `sInf` of $F$ over the finite nonempty set of schedules; reason: the infimum of a finite nonempty set is its minimum.
--   - encoding: window "interpreted as all $\tau$ labels when $\eta=0$" ($w_0=\infty$) → window length $n$ when $\eta=0$; reason: $\min\{n,\infty\}=n$.
--   - reading: "this bound is attained by a deterministic release schedule" → for every $F$-minimizing schedule, Algorithm 2 (p. 16) on it is causal, has deterministic dates and worst-case risk at most $12F^*_B+50T\phi$, with scheduled dates $0$ and $T$ keeping $\theta_0$; reason: Algorithm 2 takes "a deterministic schedule minimizing $F$" as input, the proof's bound holds for every fixed schedule, and "scheduled times zero and $T$ need not change the predictor".
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), Theorem 5.1, printed p.15, PDF p.16; Algorithm 2 and upper-bound proof printed p.16, PDF p.17; lower-bound proof printed p.18, PDF p.19; class P(Δ, η) §3.2, printed p.6, PDF p.7

import Definitions.Def_TightReleaseSchedules_Stationary_Supplement_drift_class

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace TightReleaseSchedules.Stationary.Supplement

open TightReleaseSchedules.Stationary

/-- Theorem 5.1 (printed p. 15, PDF p. 16): `R*_T(B; Δ, η) ≤ 12F*_B + 50Tϕ`, attained by
Algorithm 2 on any `F`-minimizing deterministic schedule; and, if additionally
`d ≥ 2 + log₂ max{1, B log₂ T}`, `R*_T(B; Δ, η) ≥ 2^{-35}(F*_B + Tϕ)` over all causal
randomized policies with adaptive dates. -/
theorem gradual_drift_release_schedules (T d B : ℕ) (hT : 8 ≤ T) (hd : 0 < d)
    (Δ η : ℝ) (hΔ : 0 < Δ) (hΔ₂ : Δ ≤ 1 / 2) (hη : 0 ≤ η)
    (hηT : η * T ≤ 1 / 4) (hdη : (d : ℝ) * η ≤ 1 / 8) (θ₀ : Vector d) :
    driftMinimaxRisk T d B θ₀ Δ η ≤
      ENNReal.ofReal (12 * driftOptimum T d B Δ η + 50 * T * trackingRate T d η) ∧
    (∀ τ : Fin (B + 2) → ℕ, IsSchedule T B τ → driftProgram d Δ η τ = driftOptimum T d B Δ η →
      IsCausal (windowedPolicy T d B θ₀ Δ η τ) ∧
      HasDeterministicDates (windowedPolicy T d B θ₀ Δ η τ) ∧
      driftWorstRisk θ₀ Δ η (windowedPolicy T d B θ₀ Δ η τ) ≤
        ENNReal.ofReal (12 * driftOptimum T d B Δ η + 50 * T * trackingRate T d η)) ∧
    (2 + logTwo (max 1 ((B : ℝ) * logTwo T)) ≤ (d : ℝ) →
      ENNReal.ofReal ((2 : ℝ) ^ (-35 : ℤ) *
          (driftOptimum T d B Δ η + T * trackingRate T d η)) ≤
        driftMinimaxRisk T d B θ₀ Δ η) := by sorry

end TightReleaseSchedules.Stationary.Supplement
