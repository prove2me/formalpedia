-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_lemma_5_7
-- name    : SatisfiableOrderingCSP.Optimal.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:45:43.571651+00:00
-- url     : https://prove2.me/theorems/9bf82650-f2aa-4879-bf86-971f2b371468
-- title:
--   Lemma 5.7 — exact SDP completion
-- statement:
--   Let a finite local model have each pair of distinct variables occurring together in at most one scope and each variable in at most D scope occurrences. Suppose it has an approximate SDP solution (B,W) with nonnegative error eta and eta*D<1. There are basic SDP vectors for the unchanged local model and an exact global centered covariance G which is their covariance form and satisfies G at least (1-eta*D)W. If every private block of W is positive definite on its supported centered singleton space, G is positive definite. Zero-dimensional centered spaces are included.
--
--   Differences from the source:
--   - encoding: matrices in orthonormal bases of the supported centered L2 spaces → symmetric coefficient matrices acting as bilinear forms on centered functions that vanish at zero-mass locations; reason: restriction to this subspace gives the same covariance form; positivity and the identity diagonal are tested on that subspace, including its zero-dimensional case
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Lemma 5.7, printed p. 29 (PDF p. 32); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_LocalModel

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem lemma_5_7 {n q : ℕ} (S : Scopes n) (M : LocalModel S q)
    (D : ℕ) (η : ℝ) (B W : CovarianceMatrix n q)
    (hsparse : S.Sparse) (hdegree : S.DegreeAtMost D)
    (happrox : ApproximateSDP M η B W) (hsmall : η * D < 1) :
    ∃ (V : SDPVectors M) (G : CovarianceMatrix n q),
      M.ExactCovariance G ∧ V.CovarianceIs G ∧
      (∀ f, M.Centered f → (1 - η * D) * form W f f ≤ form G f f) ∧
      (PrivateBlocksPositive M W → M.PositiveDefinite G) := by sorry

end SatisfiableOrderingCSP.Optimal
