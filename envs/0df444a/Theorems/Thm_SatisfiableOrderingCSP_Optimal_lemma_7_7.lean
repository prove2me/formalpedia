-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_lemma_7_7
-- name    : SatisfiableOrderingCSP.Optimal.lemma_7_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:50:19.041127+00:00
-- url     : https://prove2.me/theorems/243011ac-8e06-48fc-8636-16d9fdf49699
-- title:
--   Lemma 7.7 — soundness for ordered buckets
-- statement:
--   Fix a finite base instance, a sparse connected basic SDP local model with positive definite global centered covariance, and a sequence of the consistent sampling matrices of §7.2 with a uniform O(1/N) error and positive definite empirical SDP realizations. For every delta>0 there exist a positive integer K and positive real t,b0 such that, for every fixed b in (0,b0] and all sufficiently large positive even N, the following holds. Give all base variables the same partition of the real line into K ordered intervals. Let each variable's function on its multislice take values in the K-simplex, with every coordinate mean at most n0/K and every noisy coordinate influence at most t. Then its weighted average bucket acceptance under the uniform column-permutation query laws is at most value(I)+delta. Acceptance means that distinct real scores in the indicated buckets can satisfy the constraint. All occurrences of a base variable use the same function.
--
--   Differences from the source:
--   - encoding: finite indexed sets [n] and positive normalized weighted ordering instances → zero-based Fin indices, indexed repeated constraints, injective scopes, and strictly positive real weights of total one; reason: reindexing changes no instances; isolated variables remain allowed and positive total mass excludes an empty constraint list
--   - encoding: matrices in orthonormal bases of the supported centered L2 spaces → symmetric coefficient matrices acting as bilinear forms on centered functions that vanish at zero-mass locations; reason: restriction to this subspace gives the same covariance form; positivity and the identity diagonal are tested on that subspace, including its zero-dimensional case
--   - encoding: sampling matrices at every sufficiently large even length with O(1/N) errors → one error constant and length threshold before all even lengths, explicit matrix columns and counts, and an empirical local model with a common positive definite SDP realization; reason: makes the uniform error bounds, shared row counts, and covariance realization explicit without restricting real probabilities
--   - encoding: theta-noise on each multislice and theta_N=2 floor(bN/2)/N → integer counts d per supported symbol, with counts 2*floor(bN/2) on length N and floor(bN/2) on length N/2; reason: these are exactly the printed integral noise counts; zero-count ambient symbols are omitted from the cyclic support order
--   - encoding: the matrices fixed in §7.2 and common consecutive intervals → a sampling sequence with the stated uniform approximation and realization properties, and a common ordered interval partition; reason: the conclusion is independent of the particular admissible rounding choices; interval membership fixes all boundary conventions; a degenerate empty interval is permitted, and a label whose bucket is empty never accepts, so no instance is added or removed
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Lemma 7.7, printed p. 47 (PDF p. 50); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Sampling

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem lemma_7_7 (I : Instance) {q : ℕ} (M : LocalModel I.scopes q)
    (hLP : BasicLP I M) (hregular : Regularized M) (Seq : SamplingSequence M)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 0 < K ∧ ∃ t b₀ : ℝ, 0 < t ∧ 0 < b₀ ∧
      ∀ b : ℝ, 0 < b → b ≤ b₀ → ∃ N₀ : ℕ,
        ∀ N (hN : 0 < N) (hE : Even N) (hT : Seq.threshold ≤ N), N₀ ≤ N →
          ∀ (B : OrderedBuckets K) (g : Fin I.n → (Fin N → Fin q) → Fin K → ℝ),
            (∀ v x, x ∈ ((Seq.matrices N hN hE hT).histogram v).strings →
              FuchsVdGraaf.IsProbDist (g v x)) →
            (∀ v a, ((Seq.matrices N hN hE hT).histogram v).mean (fun x => g v x a) ≤
              (I.n : ℝ) / K) →
            (∀ v a i, ((Seq.matrices N hN hE hT).histogram v).noisyInfluence
              (2 * linkedCount b N) (fun x => g v x a) i ≤ t) →
            (Seq.matrices N hN hE hT).bucketValue I B g ≤ I.value + δ := by sorry

end SatisfiableOrderingCSP.Optimal
