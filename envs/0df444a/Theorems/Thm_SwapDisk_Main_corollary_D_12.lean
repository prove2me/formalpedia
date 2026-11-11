-- Prove2me | Theorems.Thm_SwapDisk_Main_corollary_D_12
-- name    : SwapDisk.Main.corollary_D_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:18:44.823189+00:00
-- url     : https://prove2.me/theorems/63ef6528-2a36-4057-956f-3abcee505b59
-- title:
--   Corollary D.12 — combined lower bounds: $V_{T,N}\ge\max\{m_T,1+(T-1)\beta_N\}\ge\max\{\sqrt{T/2},2T/(3N^2)\}$ and $V_{T,1}=T$
-- statement:
--   For every integer $T\ge2$ and $N\ge1$,
--   $$V_{T,N}\ge\max\{m_T,\,1+(T-1)\beta_N\}\ge\max\Big\{\sqrt{T/2},\,\frac{2T}{3N^2}\Big\}.$$
--   In particular $V_{T,1}=T$.
--
--   These are the lower half of the goal and its singleton endpoint.
--
--   Differences from the source:
--   - encoding: the online protocol of Eq. (A.11) with standard Borel private states and the Borel σ-field of the weak topology on P(B²₂) → `Learner`/`Adversary`/`law` of the Protocol definition: Giry σ-field on `ProbabilityMeasure Disk`, rounds indexed from 0, one kernel per `t : ℕ` (those with t ≥ T unused), private states standard Borel types; reason: the Giry and weak-topology Borel σ-fields coincide on the Polish space B²₂; the other changes are index conventions; same learners, adversaries and laws
--   - encoding: V_{T,N} = inf over dictionary learners of sup over adversaries → `VN T N` (real ⨅/⨆ over nonempty classes with values in [0, 2T]); reason: the true infimum and supremum
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 49, Corollary D.12

import Mathlib
import Definitions.Def_SwapDisk_Main_Protocol

namespace SwapDisk.Main

/-- Corollary D.12 (Combined lower bounds and the singleton endpoint), p. 49: for every integer
`T ≥ 2` and `N ≥ 1`, `V_{T,N} ≥ max{m_T, 1 + (T − 1)β_N} ≥ max{√(T/2), 2T/(3N²)}`; in
particular `V_{T,1} = T`. -/
theorem corollary_D_12 :
    (∀ T N : ℕ, 2 ≤ T → 1 ≤ N →
      max (mT T) (1 + ((T : ℝ) - 1) * betaN N) ≤ VN T N ∧
      max (Real.sqrt ((T : ℝ) / 2)) (2 * (T : ℝ) / (3 * (N : ℝ) ^ 2)) ≤
        max (mT T) (1 + ((T : ℝ) - 1) * betaN N)) ∧
    ∀ T : ℕ, 2 ≤ T → VN T 1 = T := by sorry

end SwapDisk.Main
