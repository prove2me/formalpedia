-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_theorem_4_8
-- name    : SatisfiableOrderingCSP.Optimal.theorem_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:47:45.288082+00:00
-- url     : https://prove2.me/theorems/53be75f9-e476-4835-9c08-50f5a3a46249
-- title:
--   Theorem 4.8 — effective basic LP characterization
-- statement:
--   For every finite weighted ordering instance, canonical feasibility is equivalent to existence of a basic LP solution over some positive finite ordered domain. The two directions are effective: two fixed rational-constant arithmetic programs respectively turn any given pair of canonical relaxed orders into a finite basic LP solution, and any given finite real basic LP table into a pair of canonical relaxed orders. Both programs terminate on every valid input. The LP domain may exceed the number of variables, no occupancy equalities are imposed, and the equivalence does not assert that the original constraints are simultaneously satisfiable.
--
--   Differences from the source:
--   - encoding: finite indexed sets [n] and positive normalized weighted ordering instances → zero-based Fin indices, indexed repeated constraints, injective scopes, and strictly positive real weights of total one; reason: reindexing changes no instances; isolated variables remain allowed and positive total mass excludes an empty constraint list
--   - encoding: finite and effective constructions in both directions → two fixed exact-arithmetic RAM programs on explicit order and local-distribution tables; reason: real probabilities are read exactly; no polynomial bound is asserted for these constructions
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Theorem 4.8, printed p. 20 (PDF p. 23); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Effectivity

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem theorem_4_8 :
    (∀ I : Instance, I.CanonicallyFeasible ↔
      ∃ q : ℕ, ∃ M : LocalModel I.scopes q, BasicLP I M) ∧
    EffectiveLPCharacterization := by sorry

end SatisfiableOrderingCSP.Optimal
