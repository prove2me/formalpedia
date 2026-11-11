-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_theorem_5_1
-- name    : SatisfiableOrderingCSP.Optimal.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:47:00.378641+00:00
-- url     : https://prove2.me/theorems/a79dca24-f653-4fe0-b0f1-8054f7737536
-- title:
--   Theorem 5.1 — an SDP gap from every basic LP gap
-- statement:
--   Let I admit a basic LP solution on any positive finite ordered domain, with arbitrary real probabilities and positive real instance weights. For every epsilon>0 there exists a finite unweighted lifted instance J, a lift preserving predicates and argument order, and a positive finite domain on which J admits a basic SDP solution. Its value is at most value(I)+epsilon, and any two distinct constraint occurrences of J share at most one variable. Every output predicate already occurs in I.
--
--   Differences from the source:
--   - encoding: finite indexed sets [n] and positive normalized weighted ordering instances → zero-based Fin indices, indexed repeated constraints, injective scopes, and strictly positive real weights of total one; reason: reindexing changes no instances; isolated variables remain allowed and positive total mass excludes an empty constraint list
--   - encoding: every constraint of J is lifted from I → an explicit lift preserving predicate, arity and ordered scope; reason: this records all lifted-instance clauses without changing input probabilities or weights
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Theorem 5.1, printed p. 25 (PDF p. 28); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Lifts

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem theorem_5_1 (I : Instance) {q : ℕ} (M : LocalModel I.scopes q)
    (hLP : BasicLP I M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (J : Instance) (L : Lift I J) (q' : ℕ),
      J.Unweighted ∧ J.scopes.Sparse ∧ J.value ≤ I.value + ε ∧ HasBasicSDP J q' := by sorry

end SatisfiableOrderingCSP.Optimal
