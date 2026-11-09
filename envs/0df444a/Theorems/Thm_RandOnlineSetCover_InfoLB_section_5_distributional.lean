-- Prove2me | Theorems.Thm_RandOnlineSetCover_InfoLB_section_5_distributional
-- name    : RandOnlineSetCover.InfoLB.section_5_distributional
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:00.936+00:00
-- url     : https://prove2.me/theorems/2a2721d9-e251-48bd-b6e0-d75b104bfa5e
-- title:
--   §5, concluding display — a distribution with the 1/4096 ratio
-- statement:
--   For every sufficiently large integer $n$ and every integer $m$ satisfying $(\log_2 n)^2\le m\le2^n$, there are an integer $L>0$ and a distribution $D$ on instances with exactly $m$ labeled sets and $n$ requests such that
--
--   $$
--   \operatorname{Opt}(I)\le L\quad(D\text{-almost surely}),\qquad
--   \mathbb E_{I\sim D}[|A(I)|]\ge
--   \frac1{4096}\frac{\log_2 m\log_2 n}{\log_2\log_2 m+\log_2\log_2 n}\,L
--   \quad\text{for every deterministic online algorithm }A.
--   $$
--
--   This is the distributional lower bound at the exact requested sizes. Its distribution is common to every deterministic algorithm, and its constant is the one in the paper's concluding display.
--
--   Differences from the source:
--   - reading: a distribution for which every deterministic algorithm has competitive ratio at least the displayed expression → a common positive integer L with Opt ≤ L on the support and expected cost at least the displayed expression times L; reason: this is the stronger distributional reading supplied by the proof, whose offline bound is 2k; it supports the averaging passage to randomized algorithms
--   - encoding: sufficiently large n, the whole parameter range, and binary logarithms → an existential natural threshold, exact-size finite incidence sequences, PMFs and Real.logb 2; reason: every finite instance and distribution is represented; eventual quantification implies positive logarithms without adding restrictions on m
-- source:
--   Roie Levin, STOC 2027 submission #400 (October 2026), §5, concluding display, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/400.pdf

import Mathlib
import Definitions.Def_RandOnlineSetCover_InfoLB_Model

namespace RandOnlineSetCover.InfoLB

theorem section_5_distributional :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ,
      (Real.logb 2 (n : ℝ)) ^ 2 ≤ (m : ℝ) → m ≤ 2 ^ n →
      ∃ L : ℕ, 0 < L ∧ ∃ D : InstanceDistribution m n,
        OptBound D L ∧ ∀ A : DetAlg m n,
          (1 / 4096 : ℝ) * logRatio m n * (L : ℝ) ≤ distributionCost D A := by sorry

end RandOnlineSetCover.InfoLB
