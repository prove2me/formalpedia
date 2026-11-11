-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_theorem_1_4
-- name    : SatisfiableOrderingCSP.Optimal.theorem_1_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:49:56.278623+00:00
-- url     : https://prove2.me/theorems/319104a4-344b-467b-91f9-688fa20a12f5
-- title:
--   Theorem 1.4 — basic SDP gap
-- statement:
--   For every nonempty finite ordering language of nonconstant predicates and every real epsilon>0, there is a finite instance J over that language and a positive finite ordered domain on which J has a basic SDP solution, while value(J) is at most alphaLR(language)+epsilon. The language is arbitrary and no sparsity, connectedness or covariance condition is an input hypothesis. The framework constant remains the supremum of finite IDU-plus mixture guarantees, independently of the SDP definition.
--
--   Differences from the source:
--   - encoding: finite indexed sets [n] and positive normalized weighted ordering instances → zero-based Fin indices, indexed repeated constraints, injective scopes, and strictly positive real weights of total one; reason: reindexing changes no instances; isolated variables remain allowed and positive total mass excludes an empty constraint list
--   - encoding: a fixed finite ordering language with nonconstant predicates and the minimum in Definition 4.2 → a nonempty finite set of predicates represented by their nonempty proper sets of satisfying full permutations; reason: every such finite relation is a disjunction of full strict chains; nonemptiness is the meaningful domain of the printed minimum
--   - encoding: maxima over orders and the supremum/minimum in Definition 4.2 → real suprema over finite nonempty permutation sets, a real infimum over eligible local types, and a real supremum over all finite real-coefficient mixtures; reason: scores lie in [0,1], the finite extrema are attained, eligible types exist, and the singleton uniform block gives an admissible mixture
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Theorem 1.4, printed p. 6 (PDF p. 9); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Sampling

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem theorem_1_4 (Lg : Language) (ε : ℝ) (hε : 0 < ε) :
    ∃ (J : Instance) (q : ℕ), J.Over Lg ∧ HasBasicSDP J q ∧ J.value ≤ alphaLR Lg + ε := by sorry

end SatisfiableOrderingCSP.Optimal
