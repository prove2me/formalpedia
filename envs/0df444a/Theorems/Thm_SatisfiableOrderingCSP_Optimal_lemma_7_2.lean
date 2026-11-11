-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_lemma_7_2
-- name    : SatisfiableOrderingCSP.Optimal.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:49:46.229191+00:00
-- url     : https://prove2.me/theorems/1b531d4f-a699-44f5-ad8a-9d174115e0b5
-- title:
--   Lemma 7.2 — sampling matrices at every sufficiently large even length
-- statement:
--   Fix a finite sparse local model with connected one-coordinate support graphs and a basic SDP solution with positive definite global centered covariance, as established before §7.2. There are a nonnegative finite error constant C and a length threshold such that for every sufficiently large positive even N there are sampling matrices with N columns. Every supported tuple has positive even multiplicity and unsupported tuples never occur; common row histograms have even counts. All normalized singleton and tuple counts differ from the original probabilities by at most C/N. The empirical distributions admit one basic SDP realization with a positive definite global centered covariance. C and the threshold precede N; the original probabilities may be arbitrary reals.
--
--   Differences from the source:
--   - encoding: matrices in orthonormal bases of the supported centered L2 spaces → symmetric coefficient matrices acting as bilinear forms on centered functions that vanish at zero-mass locations; reason: restriction to this subspace gives the same covariance form; positivity and the identity diagonal are tested on that subspace, including its zero-dimensional case
--   - encoding: sampling matrices at every sufficiently large even length with O(1/N) errors → one error constant and length threshold before all even lengths, explicit matrix columns and counts, and an empirical local model with a common positive definite SDP realization; reason: makes the uniform error bounds, shared row counts, and covariance realization explicit without restricting real probabilities
--   - generalization: the fixed ordering-CSP model in §7.2 → any sparse connected finite local model with a positive definite SDP realization; reason: the sampling assertion uses only local distributions and their supported tuples; the source instance supplies such a model
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Lemma 7.2, printed p. 41 (PDF p. 44); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Sampling

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem lemma_7_2 {n q : ℕ} (S : Scopes n) (M : LocalModel S q)
    (hregular : Regularized M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N → Even N →
      ∃ (A : SamplingMatrices M N) (M' : LocalModel S q) (V : SDPVectors M')
        (G : CovarianceMatrix n q),
        A.Approximates C ∧ A.Empirical M' ∧ M'.ExactCovariance G ∧
          M'.PositiveDefinite G ∧ V.CovarianceIs G := by sorry

end SatisfiableOrderingCSP.Optimal
