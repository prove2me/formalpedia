-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_lemma_7_4
-- name    : SatisfiableOrderingCSP.Optimal.lemma_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:48:55.884479+00:00
-- url     : https://prove2.me/theorems/a1c446d0-9fa4-4e2c-b4aa-fccb3a0b9cd4
-- title:
--   Lemma 7.4 — uniform influence estimates
-- statement:
--   Fix alpha>0 and a finite bound Q on the number of supported symbols. First, for every sufficiently small fixed b>0 there exist a nonnegative finite Imax and a length threshold, uniformly over all alpha-balanced histograms with at most Q supported symbols and all valid integral noise counts d with d/n in [b/2,b], such that the sum of d-noisy influences of every real function is at most Imax times its squared L2 norm. Second, for every t0>0 there exist b1>0 and lambda>0, chosen before b and the alphabet length, such that for every fixed b in (0,b1] and every sufficiently large positive even N the following holds. For any alpha-balanced even-count histogram, its half histogram, any pairing law uniform on unlabeled pair partitions, and any function with values in [-1,1], an input coordinate of noisy influence at least t0 projects to a coordinate of restricted noisy influence at least lambda with probability at least lambda. The two noise counts are 2 floor(bN/2) and floor(bN/2). Fiber names may follow any distribution consistent with uniform unlabeled pairings.
--
--   Differences from the source:
--   - encoding: theta-noise on each multislice and theta_N=2 floor(bN/2)/N → integer counts d per supported symbol, with counts 2*floor(bN/2) on length N and floor(bN/2) on length N/2; reason: these are exactly the printed integral noise counts; zero-count ambient symbols are omitted from the cyclic support order
--   - encoding: uniform random pairings with arbitrary fiber names → any finite probability law supported on two-to-one maps whose unlabeled partition marginal is uniform; reason: this preserves the full permitted naming freedom, including correlations with the partition
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Lemma 7.4, printed p. 45 (PDF p. 48); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Multislices

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem lemma_7_4 (α : ℝ) (hα : 0 < α) (Q : ℕ) :
    (∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
      ∃ Imax : ℝ, 0 ≤ Imax ∧ ∃ n₀ : ℕ, ∀ n q : ℕ, n₀ ≤ n →
        ∀ (H : Histogram n q), H.Balanced α → H.support.card ≤ Q →
          ∀ d : ℕ, H.NoiseValid d → b/2 ≤ (d : ℝ)/n → (d : ℝ)/n ≤ b →
            ∀ f : (Fin n → Fin q) → ℝ,
              (∑ i, H.noisyInfluence d f i) ≤ Imax * H.mean (fun x => (f x)^2)) ∧
    (∀ t₀ : ℝ, 0 < t₀ → ∃ b₁ lam : ℝ, 0 < b₁ ∧ 0 < lam ∧
      ∀ b : ℝ, 0 < b → b ≤ b₁ → ∃ N₀ : ℕ,
        ∀ N q : ℕ, N₀ ≤ N → 0 < N → Even N →
          ∀ (H : Histogram N q) (h : Histogram (N/2) q),
            H.Balanced α → H.support.card ≤ Q → H.EvenCounts → HalfHistogram H h →
              ∀ (p : (Fin N → Fin (N/2)) → ℝ), PairingLaw p →
                ∀ f : (Fin N → Fin q) → ℝ,
                  (∀ x ∈ H.strings, -1 ≤ f x ∧ f x ≤ 1) →
                  ∀ i : Fin N, t₀ ≤ H.noisyInfluence (2 * linkedCount b N) f i →
                    lam ≤ ∑ π, p π * (if lam ≤ h.noisyInfluence (linkedCount b N)
                      (fun y => f (y ∘ π)) (π i) then 1 else 0)) := by sorry

end SatisfiableOrderingCSP.Optimal
