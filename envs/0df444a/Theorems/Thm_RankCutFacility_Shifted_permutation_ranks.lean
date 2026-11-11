-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_permutation_ranks
-- name    : RankCutFacility.Shifted.permutation_ranks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:55.14926+00:00
-- url     : https://prove2.me/theorems/27910872-e441-48b9-8bcc-02ad9e084ffd
-- title:
--   Lemma 3.1 — Permutation ranks, anchor identity and conditional uniformity
-- statement:
--   Let $n\ge1$ and let $C$ be a nonempty set of $k$ distinct copy labels among $n$ labels. Permutations are sampled uniformly. Let $T$ be the first rank occupied by $C$, $p$ its anchor identity, and let the rank set record every rank occupied by $C$.
--
--   Lemma 3.1. Fix a set C of k labeled copies in a uniformly random permutation of n copies. Let T be its first rank and p the copy at that rank. The identity p is uniform in C and independent of the set of ranks occupied by C. For 1 ≤ j ≤ n − k + 1,
--   $$
--   \mathbb P(T\ge j)=\frac{\binom{n-j+1}{k}}{\binom nk}.\tag{2}
--   $$
--   In particular, for an integer h ≥ 0,
--   $$
--   \mathbb P(T>h)\le\left(1-\frac kn\right)^h,\tag{3}
--   $$
--   where the left side is zero when h > n − k and the right side is understood as one at h = 0. Conditional on the ordered prefix through T, each fixed remaining copy has a uniform rank in {T + 1, . . . , n}. Moreover, after conditioning on p and on the relative order outside C, the rank set of C is still a uniformly random k-subset of [n].
--
--   This supplies the complete permutation facts used by both cluster accounts.
--
--   Differences from the source:
--   - encoding: uniform or conditional permutation expectation → finite arithmetic averages over all permutations or the indicated nonempty fibers; reason: these are exactly the source finite uniform laws; no integration or measurability assumption is needed
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), Lemma 3.1, printed p. 7 (PDF p. 9), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
theorem permutation_ranks {n : ℕ} (hn : 0 < n) (C : Finset (Fin n)) (hC : C.Nonempty) :
    (∀ p ∈ C, prob (Finset.univ : Finset (Arrival n)) (fun π => anchor C π = some p) = 1 / (C.card : ℝ)) ∧
    (∀ p ∈ C, ∀ R : Finset ℕ,
      prob (Finset.univ : Finset (Arrival n)) (fun π => anchor C π = some p ∧ ranks C π = R) =
      prob (Finset.univ : Finset (Arrival n)) (fun π => anchor C π = some p) *
      prob (Finset.univ : Finset (Arrival n)) (fun π => ranks C π = R)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ n-C.card+1 →
      prob (Finset.univ : Finset (Arrival n)) (fun π => j ≤ firstRank C π) =
        (Nat.choose (n-j+1) C.card : ℝ) / (Nat.choose n C.card : ℝ)) ∧
    (∀ h : ℕ, prob (Finset.univ : Finset (Arrival n)) (fun π => h < firstRank C π) ≤
      (1 - (C.card : ℝ)/(n : ℝ))^h) ∧
    (∀ h : ℕ, n-C.card < h →
      prob (Finset.univ : Finset (Arrival n)) (fun π => h < firstRank C π) = 0) ∧
    (∀ π : Arrival n, ∀ u : Fin n, firstRank C π < rank π u →
      ∀ j : ℕ, firstRank C π < j → j ≤ n →
        prob (prefixFiber C π) (fun σ => rank σ u = j) = 1 / ((n-firstRank C π : ℕ) : ℝ)) ∧
    (∀ p ∈ C, ∀ o : List (Fin n), (identityOutsideFiber C p o).Nonempty →
      ∀ R : Finset ℕ, R ⊆ Finset.Icc 1 n → R.card = C.card →
        prob (identityOutsideFiber C p o) (fun π => ranks C π = R) =
          1 / (Nat.choose n C.card : ℝ)) := by sorry
end RankCutFacility.Shifted
