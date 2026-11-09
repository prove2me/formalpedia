-- Prove2me | Theorems.Thm_QGraphColl_lemma_2_8
-- name    : QGraphColl.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:35.136432+00:00
-- url     : https://prove2.me/theorems/3e5350ed-7f99-4beb-b35e-4cfc29940cb1
-- title:
--   Lemma 2.8 — bipartite collision test with $\tilde O(\sqrt a+\sqrt b+(a^2bk)^{1/6})$ queries
-- statement:
--   Let $n=|V|\ge2$ and let $G$ be bipartite with sides $A,B$ of sizes $a,b$, and $k\ge0$ an integer. For every $c>0$ there are $C,K$ (independent of $V$, $G$, $k$) and a test with
--   $$T\le C\left(\sqrt a+\sqrt b+(a^2bk)^{1/6}\right)(\log_2 n)^K\qquad(2.1)$$
--   queries which, with error at most $n^{-c}$, accepts every positive input and rejects every negative input with $|M\cap B|\le k$.
--
--   This is the test of the recorded dense graphs in Lemma 4.5.
--
--   Differences from the source:
--   - encoding: Õ(B) and 'the assigned error probability' → ∃ C, K (chosen after the error exponent c, before the vertex type and all parameters) with T ≤ C·B·(log₂ n)^K, n = |V| ≥ 2, and error ≤ n^{−c} for every c > 0; reason: the paper's conventions: Õ suppresses factors polynomial in log n and logarithms are base two (p.12); error probabilities are inverse polynomial in n (p.14)
--   - reading: the named procedure bipartite_test(G, A, B, k) (Algorithm 12) has the stated cost and guarantees → there is a T-query algorithm (QueryAlg, workspace Fin m) with that cost and those guarantees; reason: the procedure is a schema over black-box subroutines, so it is not one fixed object; the existence of a procedure with the printed cost and guarantees is what later proofs use (paper.md decision 4)
--   - encoding: count bound k → k : ℕ; reason: k bounds a cardinality; a real bound k ≥ 0 defines the same domain as ⌊k⌋, whose cost bound is no larger
--   - generalization: G bipartite with vertex sets A and B (V(G) = A ∪ B) → IsSides G A B on a vertex type that may contain further labels outside A ∪ B; reason: labels outside A ∪ B are isolated; taking V = A ∪ B gives the source's statement
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 2.8 and (2.1), p.14 (restated with proof, p.47; Algorithm 12 bipartite_test)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_restrict
import Definitions.Def_QGraphColl_eventProb

open QAlgorithms

namespace QGraphColl

/-- **Lemma 2.8** (Bipartite collision test; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.14, restated p.47). Let `G` be bipartite with
sides `A, B` of sizes `a, b`. The procedure `bipartite_test(G, A, B, k)` accepts every positive
input and rejects negative inputs satisfying `|M ∩ B| ≤ k`, with query complexity
`Õ(√a + √b + (a²bk)^{1/6})` (2.1).

**Formalization Note.**
* `Õ(B)` is `C · B · (log₂ n)^K` with `C, K` chosen after the error exponent `c` and before
  the vertex type and all parameters; "the assigned error probability" is `n^{-c}` for every `c > 0`
  (p.14: error probabilities are inverse polynomial in `n`), with `n = |V| ≥ 2`.
* The named procedure `bipartite_test` (Algorithm 12) is stated as the existence of a `T`-query
  algorithm computing `gc G` with error `≤ n^{-c}` on all positive inputs and all negative inputs
  with `|M ∩ B| ≤ k`.
* The count bound `k` is a natural number (a bound on a cardinality; a real bound `k ≥ 0` is
  equivalent to `⌊k⌋`, whose cost is no larger). Labels outside `A ∪ B` are allowed (isolated). -/
theorem lemma_2_8 :
    ∀ c : ℝ, 0 < c → ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (A B : Finset V), IsSides G A B → ∀ k : ℕ,
        ∃ T : ℕ, (T : ℝ) ≤ C * (Real.sqrt (A.card : ℝ) + Real.sqrt (B.card : ℝ) +
              ((A.card : ℝ) ^ 2 * B.card * k) ^ ((1 : ℝ) / 6)) *
            Real.logb 2 (Fintype.card V : ℝ) ^ K ∧
          ∃ (m : ℕ) (Alg : QueryAlg V Bool (Fin m) T) (out : (V × Bool) × Fin m → Bool),
            Alg.ComputesWithError out
              (dom fun x => gc G x = true ∨ (gc G x = false ∧ (marked x ∩ B).card ≤ k))
              (gc G) ((Fintype.card V : ℝ) ^ (-c)) := by sorry

end QGraphColl
