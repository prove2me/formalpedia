-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_theorem_4_5
-- name    : SatisfiableOrderingCSP.Optimal.theorem_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:45:56.626963+00:00
-- url     : https://prove2.me/theorems/7004096d-a38a-41aa-b979-74a4bd9232eb
-- title:
--   Theorem 4.5 — framework value and canonical gaps
-- statement:
--   For every nonempty finite ordering language of nonconstant predicates, alphaLR equals the infimum of the values of all finite canonically feasible instances over that language. In particular, for each epsilon>0 there is such an instance whose value is strictly less than alphaLR+epsilon. Mathematical instances have strictly positive real weights summing to one. Both canonical orders may differ, and the optimum always ranges over all permutations of the variable set.
--
--   Differences from the source:
--   - encoding: finite indexed sets [n] and positive normalized weighted ordering instances → zero-based Fin indices, indexed repeated constraints, injective scopes, and strictly positive real weights of total one; reason: reindexing changes no instances; isolated variables remain allowed and positive total mass excludes an empty constraint list
--   - encoding: a fixed finite ordering language with nonconstant predicates and the minimum in Definition 4.2 → a nonempty finite set of predicates represented by their nonempty proper sets of satisfying full permutations; reason: every such finite relation is a disjunction of full strict chains; nonemptiness is the meaningful domain of the printed minimum
--   - encoding: maxima over orders and the supremum/minimum in Definition 4.2 → real suprema over finite nonempty permutation sets, a real infimum over eligible local types, and a real supremum over all finite real-coefficient mixtures; reason: scores lie in [0,1], the finite extrema are attained, eligible types exist, and the singleton uniform block gives an admissible mixture
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Theorem 4.5, printed p. 18 (PDF p. 21); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Transformations

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem theorem_4_5 (Lg : Language) :
    alphaLR Lg = sInf {x | ∃ I : Instance, I.Over Lg ∧ I.CanonicallyFeasible ∧ x = I.value} ∧
    ∀ ε : ℝ, 0 < ε → ∃ I : Instance,
      I.Over Lg ∧ I.CanonicallyFeasible ∧ I.value < alphaLR Lg + ε := by sorry

end SatisfiableOrderingCSP.Optimal
