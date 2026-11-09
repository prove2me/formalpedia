-- Prove2me | Theorems.Thm_RandOnlineSetCover_InfoLB_lemma_3_1
-- name    : RandOnlineSetCover.InfoLB.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:39.730198+00:00
-- url     : https://prove2.me/theorems/e4843581-ba26-4386-ab86-3ce9aa8c226d
-- title:
--   Lemma 3.1 — the hard inner distribution
-- statement:
--   For every integer $k>1$ there is a distribution $D$ of online set-cover instances with $512k^2$ labeled sets and a common number $n_{\rm in}\le k4^k$ of requested elements such that
--
--   $$
--   \operatorname{Opt}(I)\le2k\quad(D\text{-almost surely}),\qquad
--   \mathbb E_{I\sim D}[|A(I)|]\ge\frac{k(k+1)}4
--   \quad\text{for every deterministic online algorithm }A.
--   $$
--
--   The distribution is existential and is chosen before the algorithm. This provides the inner parameters required for amplification.
--
--   Differences from the source:
--   - generalization: instances with n_in ≤ k4^k requested elements → one fixed n_in ≤ k4^k shared by the whole distribution; reason: the construction has the same batch sizes at each depth on every path, so the stronger fixed-length existential includes the stated result
--   - encoding: a distribution and an almost-sure optimum bound → a PMF on the finite type of valid incidence sequences and a bound at every positive-mass instance; reason: finite labels and fixed length make the instance space finite; supportwise bounds are equivalent to probability one
-- source:
--   Roie Levin, STOC 2027 submission #400 (October 2026), Lemma 3.1, p. 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/400.pdf

import Mathlib
import Definitions.Def_RandOnlineSetCover_InfoLB_Model

namespace RandOnlineSetCover.InfoLB

theorem lemma_3_1 (k : ℕ) (hk : 1 < k) :
    ∃ n : ℕ, n ≤ k * 4 ^ k ∧
      ∃ D : InstanceDistribution (512 * k ^ 2) n,
        OptBound D (2 * k) ∧
        ∀ A : DetAlg (512 * k ^ 2) n,
          (k : ℝ) * (k + 1) / 4 ≤ distributionCost D A := by sorry

end RandOnlineSetCover.InfoLB
