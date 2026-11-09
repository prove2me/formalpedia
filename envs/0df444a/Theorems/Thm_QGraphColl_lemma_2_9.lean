-- Prove2me | Theorems.Thm_QGraphColl_lemma_2_9
-- name    : QGraphColl.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:29.739268+00:00
-- url     : https://prove2.me/theorems/f099e1d0-11aa-495f-abaa-a2475b001d48
-- title:
--   Lemma 2.9 — few marked vertices in a cover: a test with $\tilde O(\sqrt n(1+k)^{1/6})$ queries
-- statement:
--   Let $n\ge2$, let $G$ have at most $n$ vertices and let $U$ be a known vertex cover of $G$, and $k\ge0$ an integer. For every $c>0$ there are $C,K$ (independent of $n$, $G$, $U$, $k$) and a test with
--   $$T\le C\sqrt n\,(1+k)^{1/6}(\log_2 n)^K$$
--   queries which, with error at most $n^{-c}$, accepts every positive input and rejects every negative input with $|M\cap U|\le k$.
--
--   This test removes the edges at high-degree vertices in the degree-reduction step (Lemma 4.2).
--
--   Differences from the source:
--   - encoding: Õ(√n (1+k)^{1/6}) and the assigned error, n the stated vertex bound → ∃ C, K (after c, before n) with T ≤ C·√n·(1+k)^{1/6}·(log₂ n)^K and error ≤ n^{−c} for every c > 0, n ≥ 2, |V| ≤ n; reason: the paper's conventions (pp.12, 14); n here is the stated upper bound on the vertex count
--   - reading: there is a test that accepts every positive input and rejects negative inputs satisfying |M ∩ U| ≤ k → a T-query QueryAlg computing gc G on {gc G} ∪ {¬gc G ∧ |M ∩ U| ≤ k}; reason: the bound restricts only the negative inputs (pp.14–15)
--   - encoding: count bound k → k : ℕ; reason: k bounds a cardinality; a real bound k ≥ 0 defines the same domain as ⌊k⌋, whose cost bound is no larger
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 2.9, p.14 (restated with proof, p.48)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_restrict
import Definitions.Def_QGraphColl_eventProb

open QAlgorithms

namespace QGraphColl

/-- **Lemma 2.9** (Few marked vertices in a cover; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.14, restated p.48). Let `G` have at most
`n` vertices and let `U` be a known vertex cover. There is a test using `Õ(√n (1 + k)^{1/6})`
queries that accepts every positive input and rejects negative inputs satisfying `|M ∩ U| ≤ k`.

**Formalization Note.**
* Here `n ≥ 2` is the stated upper bound on the number of vertices (`|V| ≤ n`), and `Õ` hides
  `(log₂ n)^K`. `C, K` are chosen after the error exponent `c` and before `n`; the error is
  `n^{-c}` for every `c > 0` (p.14).
* "A test that accepts every positive input and rejects negative inputs satisfying the bound": an
  algorithm computing `gc G` with error `≤ n^{-c}` on all positive inputs and all negative inputs
  with `|M ∩ U| ≤ k`. The count bound `k` is a natural number. -/
theorem lemma_2_9 :
    ∀ c : ℝ, 0 < c → ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ n : ℕ, 2 ≤ n → ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V ≤ n →
      ∀ (G : SimpleGraph V) (U : Finset V), IsCover G U → ∀ k : ℕ,
        ∃ T : ℕ, (T : ℝ) ≤ C * (Real.sqrt (n : ℝ) * (1 + (k : ℝ)) ^ ((1 : ℝ) / 6)) *
            Real.logb 2 (n : ℝ) ^ K ∧
          ∃ (m : ℕ) (A : QueryAlg V Bool (Fin m) T) (out : (V × Bool) × Fin m → Bool),
            A.ComputesWithError out
              (dom fun x => gc G x = true ∨ (gc G x = false ∧ (marked x ∩ U).card ≤ k))
              (gc G) ((n : ℝ) ^ (-c)) := by sorry

end QGraphColl
