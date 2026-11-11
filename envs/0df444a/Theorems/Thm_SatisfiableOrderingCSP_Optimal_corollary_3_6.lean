-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_corollary_3_6
-- name    : SatisfiableOrderingCSP.Optimal.corollary_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:45:48.094215+00:00
-- url     : https://prove2.me/theorems/cec589b7-d821-462f-ab84-37439c615ad3
-- title:
--   Corollary 3.6 — finite mixtures replace weak transformations
-- statement:
--   Let T be any weak two-order transformation and D any finite set of local types. Suppose that T satisfies every constraint of every type in D with probability at least beta, uniformly over all input sizes, input orders and injective occurrences of those types. For every epsilon>0 there is a finite real-coefficient mixture of IDU-plus combinations with the same uniform per-constraint guarantee beta-epsilon for every type in D. D may be empty and beta is an arbitrary real number.
--
--   Differences from the source:
--   - encoding: finite argument sets and patterns → zero-based Fin indices and permutations in argument order; reason: reindexing changes no local type
--   - encoding: weak transformations for n>=1 and restriction to empty subsets → normalized laws also at n=0; reason: the empty permutation is unique, so its probability law adds no choice or restriction
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Corollary 3.6, printed p. 14 (PDF p. 17); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Transformations

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem corollary_3_6 (T : WeakTransformation) (D : Finset LocalType)
    (β : ℝ) (hT : ∀ d ∈ D, T.Guarantees d β) (ε : ℝ) (hε : 0 < ε) :
    ∃ ν : Mixture, ∀ d ∈ D, ν.Guarantees d (β - ε) := by sorry

end SatisfiableOrderingCSP.Optimal
