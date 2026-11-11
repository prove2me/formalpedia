-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_theorem_6_1
-- name    : SatisfiableOrderingCSP.Optimal.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:46:31.786631+00:00
-- url     : https://prove2.me/theorems/7dc4e402-8522-4c63-8a02-b29da8f0e800
-- title:
--   Theorem 6.1 — SDP solutions from common increasing embeddings
-- statement:
--   Let M be any finite local model over a positive finite ordered domain, with arbitrary real probabilities and sparse scopes: each pair of distinct variables occurs together in at most one local distribution. There exists a positive finite target domain and a finite real distribution of strictly increasing embeddings such that applying one independently sampled embedding simultaneously to every coordinate of each local tuple gives a model admitting basic SDP vectors and a positive definite exact global centered covariance. The same embedding law is used at all scopes and for all singleton distributions. No connectedness, initial SDP feasibility or positive definiteness is assumed.
--
--   Differences from the source:
--   - encoding: matrices in orthonormal bases of the supported centered L2 spaces → symmetric coefficient matrices acting as bilinear forms on centered functions that vanish at zero-mass locations; reason: restriction to this subspace gives the same covariance form; positivity and the identity diagonal are tested on that subspace, including its zero-dimensional case
--   - encoding: a common finite random increasing embedding → a finite probability vector and a family of strictly increasing maps with explicit pushforward equations; reason: the same sampled map acts on all coordinates and is independent of the old tuple
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Theorem 6.1, printed p. 30 (PDF p. 33); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Lifts

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem theorem_6_1 {n q : ℕ} (S : Scopes n) (M : LocalModel S q)
    (hsparse : S.Sparse) :
    ∃ (q' : ℕ) (F : IncreasingMixture q q') (M' : LocalModel S q')
      (V : SDPVectors M') (G : CovarianceMatrix n q'),
      F.Pushes M M' ∧ M'.ExactCovariance G ∧ M'.PositiveDefinite G ∧ V.CovarianceIs G := by sorry

end SatisfiableOrderingCSP.Optimal
