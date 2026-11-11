-- Prove2me | Theorems.Thm_SwapDisk_Main_theorem_1_1
-- name    : SwapDisk.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:19:03.027197+00:00
-- url     : https://prove2.me/theorems/614a4c42-94ca-471f-86c5-7607f1a8472e
-- title:
--   Theorem 1.1 — the price of a fixed dictionary: $c(\sqrt T+T/N^2)\le V_{T,N}\le\min\{T,C(\sqrt T+T/N^2)\}$, $V_{T,1}=T$, upper bound by a deterministic dictionary
-- statement:
--   There are universal constants $c,C>0$ such that, for all integers $T\ge2$ and $N\ge1$,
--   $$c\Big(\sqrt T+\frac T{N^2}\Big)\le V_{T,N}\le\min\Big\{T,\;C\Big(\sqrt T+\frac T{N^2}\Big)\Big\}.$$
--   Moreover $V_{T,1}=T$. A confidence-independent learner attains the upper bound with a deterministic dictionary: for every $T,N$ some learner whose actions lie in a fixed tuple of $N$ points has $\sup_D\mathbb E_{A,D}R_T\le\min\{T,C(\sqrt T+T/N^2)\}$. The lower bound permits privately randomized dictionaries: $V_{T,N}$ is the infimum over every admissible learner with an ex ante dictionary of at most $N$ points, random or not, of the supremum over every admissible (adaptive, randomized) adversary of $\mathbb E[R_T]$, with $R_T$ the realized full swap regret over all Borel deviations.
--
--   This is the paper's main theorem: with a dictionary of at most $N$ points fixed before play, the minimax realized full swap regret on the disk is $\Theta(\sqrt T+T/N^2)$.
--
--   Differences from the source:
--   - encoding: the online protocol of Eq. (A.11) with standard Borel private states and the Borel σ-field of the weak topology on P(B²₂) → `Learner`/`Adversary`/`law` of the Protocol definition: Giry σ-field on `ProbabilityMeasure Disk`, rounds indexed from 0, one kernel per `t : ℕ` (those with t ≥ T unused), private states standard Borel types; reason: the Giry and weak-topology Borel σ-fields coincide on the Polish space B²₂; the other changes are index conventions; same learners, adversaries and laws
--   - encoding: V_{T,N} over learners with an ex ante, possibly privately randomized, dictionary of at most N points → `VN T N`: real ⨅ over `{L // IsDictLearner T N L}` of real ⨆ over adversaries of `expectedRegret`; reason: §A.5's encoding; the classes are nonempty and every value lies in [0, 2T], so these are the true infimum and supremum
--   - encoding: a confidence-independent learner attains the upper bound with a deterministic dictionary → ∃ L with `IsDetDictLearner T N L` and `expectedRegret T L D ≤ min{T, C(√T + T/N²)}` for every adversary D; reason: the learner takes no δ; a bound for every adversary is the bound on the supremum
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 1, Theorem 1.1

import Mathlib
import Definitions.Def_SwapDisk_Main_Protocol

namespace SwapDisk.Main

/-- Theorem 1.1 (The price of a fixed dictionary), p. 1: universal `c, C > 0` such that for all
integers `T ≥ 2`, `N ≥ 1`, `c(√T + T/N²) ≤ V_{T,N} ≤ min{T, C(√T + T/N²)}`, the upper bound
attained by a learner with a deterministic dictionary of at most `N` points (against every
adversary), and `V_{T,1} = T`. `V_{T,N}` ranges over every admissible learner with an ex ante,
possibly privately randomized, dictionary. -/
theorem theorem_1_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ T N : ℕ, 2 ≤ T → 1 ≤ N →
        c * (Real.sqrt T + (T : ℝ) / (N : ℝ) ^ 2) ≤ VN T N ∧
        VN T N ≤ min (T : ℝ) (C * (Real.sqrt T + (T : ℝ) / (N : ℝ) ^ 2)) ∧
        ∃ L : Learner, IsDetDictLearner T N L ∧
          ∀ D : Adversary,
            expectedRegret T L D ≤ min (T : ℝ) (C * (Real.sqrt T + (T : ℝ) / (N : ℝ) ^ 2))) ∧
      ∀ T : ℕ, 2 ≤ T → VN T 1 = T := by sorry

end SwapDisk.Main
