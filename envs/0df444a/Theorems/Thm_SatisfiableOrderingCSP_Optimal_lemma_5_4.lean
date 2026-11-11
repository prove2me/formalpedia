-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_lemma_5_4
-- name    : SatisfiableOrderingCSP.Optimal.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:46:36.781817+00:00
-- url     : https://prove2.me/theorems/1f33e0e1-905c-4868-b862-ca1b1b2a6fc1
-- title:
--   Lemma 5.4 — sparse lift
-- statement:
--   For any finite positive-real-weighted ordering instance I and epsilon>0 there exists a finite unweighted instance J on copies of its variables, with every constraint lifted from a constraint occurrence of I in the same argument order, such that distinct constraint occurrences share at most one variable and value(J) is at most value(I)+epsilon. Every basic LP solution for I, over any positive finite domain and with arbitrary real probabilities, induces a basic LP solution for J by exactly copying its singleton and constraint distributions along the lift maps.
--
--   Differences from the source:
--   - encoding: finite indexed sets [n] and positive normalized weighted ordering instances → zero-based Fin indices, indexed repeated constraints, injective scopes, and strictly positive real weights of total one; reason: reindexing changes no instances; isolated variables remain allowed and positive total mass excludes an empty constraint list
--   - encoding: instances on copies with distributions copied from I → explicit variable and constraint maps with argument-order equality and probability-table pullback; reason: the maps express the printed lift without requiring every original constraint to appear
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Lemma 5.4, printed p. 26 (PDF p. 29); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Lifts

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem lemma_5_4 (I : Instance) (ε : ℝ) (hε : 0 < ε) :
    ∃ (J : Instance) (L : Lift I J), J.Unweighted ∧ J.scopes.Sparse ∧
      J.value ≤ I.value + ε ∧
      ∀ q (M : LocalModel I.scopes q), BasicLP I M →
        ∃ M' : LocalModel J.scopes q, BasicLP J M' ∧ L.Copies M M' := by sorry

end SatisfiableOrderingCSP.Optimal
