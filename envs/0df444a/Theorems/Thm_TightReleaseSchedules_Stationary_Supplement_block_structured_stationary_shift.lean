-- Prove2me | Theorems.Thm_TightReleaseSchedules_Stationary_Supplement_block_structured_stationary_shift
-- name    : TightReleaseSchedules.Stationary.Supplement.block_structured_stationary_shift
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T04:20:56.239916+00:00
-- url     : https://prove2.me/theorems/f526f59a-18c5-4cb6-939d-63ac473680fb
-- title:
--   Theorem 4.3 — block-structured stationary shift, minimax risk between 2^{-25}E*_B and 2E*_B
-- statement:
--   Let $T,d\ge1$ and $B\ge0$ be integers. Let $\theta_0\in\mathbb R^d$ be the pretrained vector, and partition the coordinates into known nonempty blocks $S_1,\dots,S_K$ of sizes $d_i$. Let the radii satisfy
--
--   $$
--   0<\Delta_i\le1,\qquad \sum_{i=1}^K\Delta_i^2\le1 .
--   $$
--
--   The target is constant and lies in the block class $\|P_{S_i}(\theta-\theta_0)\|_2\le\Delta_i$ for every $i$. Write $E^*_B$ for the minimum over integer schedules of the block program $E(\tau)=\sum_{j=0}^{B}L_j\sum_{i}\min\{d_i/\tau_j,\Delta_i^2\}$, with $d_i/0=\infty$. Then:
--
--   1. The minimax risk over the block class is at most $2E^*_B$.
--   2. The bound is attained by a deterministic release grid. For every schedule $\tau$ with $E(\tau)=E^*_B$, the block-projected anchored-average grid on $\tau$ is causal and has fixed release dates. Its worst-case risk over the block class is at most $2E^*_B$.
--   3. If $T\ge8$ and
--
--   $$
--   \min_i d_i\ \ge\ 1+\log_2\max\{1,\,KB\log_2T\},
--   $$
--
--   then the minimax risk is at least $2^{-25}E^*_B$, over all randomized causal policies with at most $B$ releases, including adaptively timed ones.
--
--   The upper bound needs neither $T\ge8$ nor the dimension condition. The theorem extends the stationary rate of Theorem 4.1 to shift radii that differ across known coordinate blocks. Its corollary shows that a block with $T\Delta_i^2\le d_i$ can be left at its pretrained value without changing the minimax order.
--
--   **Formalization Note** Risks are extended nonnegative reals and the real bounds enter through `ENNReal.ofReal`. The minimax value is the set infimum over every seed space and every causal policy, as in the base mission.
--
--   Differences from the source:
--   - encoding: rounds $t=1,\dots,T$, randomized causal policies with at most $B$ releases, expected half-squared risk and $\inf_\pi\sup_\theta$ → index $i$ of `Fin T` is round $i+1$, the base mission's `ReleasePolicy`/`IsCausal` on an arbitrary seed space, `ENNReal`-valued `policyRisk` compared with `ENNReal.ofReal` of the real bound, and the minimax value as a set infimum over all seed spaces and causal policies; reason: the base mission's conventions, which change no instance and exclude no competitor with infinite risk.
--   - reading: blocks $S_1,\dots,S_K$ partitioning the coordinates with sizes $d_1,\dots,d_K$ → nonempty, pairwise disjoint `Finset (Fin d)` covering `Fin d`; reason: the parts of a partition are nonempty.
--   - encoding: $\min\{d_i/\tau_j,\Delta_i^2\}$ with $d_i/0=\infty$ → `if τ_j = 0 then Δ_i² else min (d_i/τ_j) Δ_i²`; reason: $\min\{\infty,\Delta_i^2\}=\Delta_i^2$, the same value for every schedule.
--   - encoding: $E^*_B=\min_\tau E(\tau)$ → the real `sInf` of $E$ over the finite nonempty set of schedules; reason: the infimum of a finite nonempty set is its minimum.
--   - reading: "the upper bound uses a deterministic release grid" → for every $E$-minimizing schedule, the grid of block-projected anchored averages of the proof (p. 13) is causal, has deterministic dates, and has worst-case risk at most $2E^*_B$; reason: this is the policy the proof constructs, and the proof's bound holds for every fixed schedule.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), Theorem 4.3, printed p.13, PDF p.14; proof printed pp.13–14, PDF pp.14–15

import Definitions.Def_TightReleaseSchedules_Stationary_Supplement_block_class

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace TightReleaseSchedules.Stationary.Supplement

open TightReleaseSchedules.Stationary

/-- Theorem 4.3 (printed p. 13, PDF p. 14): upper bound `2E*_B` unconditionally, attained by
the deterministic block-projected grid on any minimizing schedule; lower bound `2^{-25}E*_B`
over all causal randomized policies with adaptive dates when `T ≥ 8` and
`min_i d_i ≥ 1 + log₂ max{1, KB log₂ T}`. -/
theorem block_structured_stationary_shift (T d B K : ℕ) (hT : 0 < T) (hd : 0 < d)
    (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S)
    (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (hΔ₁ : ∀ i, Δ i ≤ 1)
    (hΔsum : ∑ i, Δ i ^ 2 ≤ 1) (θ₀ : Vector d) :
    blockMinimaxRisk T d B K θ₀ S Δ ≤ ENNReal.ofReal (2 * blockOptimum T B S Δ) ∧
    (∀ τ : Fin (B + 2) → ℕ, IsSchedule T B τ → blockProgram S Δ τ = blockOptimum T B S Δ →
      IsCausal (blockGridPolicy T d B K θ₀ S Δ τ) ∧
      HasDeterministicDates (blockGridPolicy T d B K θ₀ S Δ τ) ∧
      blockWorstRisk θ₀ S Δ (blockGridPolicy T d B K θ₀ S Δ τ) ≤
        ENNReal.ofReal (2 * blockOptimum T B S Δ)) ∧
    (8 ≤ T →
      (∀ i, 1 + logTwo (max 1 ((K : ℝ) * B * logTwo T)) ≤ ((S i).card : ℝ)) →
      ENNReal.ofReal ((2 : ℝ) ^ (-25 : ℤ) * blockOptimum T B S Δ) ≤
        blockMinimaxRisk T d B K θ₀ S Δ) := by sorry

end TightReleaseSchedules.Stationary.Supplement
