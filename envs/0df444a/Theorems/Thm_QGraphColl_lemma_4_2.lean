-- Prove2me | Theorems.Thm_QGraphColl_lemma_4_2
-- name    : QGraphColl.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:12.477094+00:00
-- url     : https://prove2.me/theorems/753ea0a3-f316-42eb-8cb0-b92066b2a2af
-- title:
--   Lemma 4.2 — degree reduction with $\tilde O(n^{3/4}/d^{1/4})$ queries
-- statement:
--   Let $n=|V|\ge2$, let $G$ be a graph on $V$ and $1\le d\le n$. For every $c>0$ there are $C,K$ (independent of $V$, $G$, $d$) and an algorithm with
--   $$T\le C\,\frac{n^{3/4}}{d^{1/4}}\,(\log_2 n)^K$$
--   queries that either reports a collision or returns a graph $G'\subseteq G$ on the same labels, such that
--
--   1. every returned graph has maximum degree at most $d$;
--   2. on every negative input, with probability at least $1-n^{-c}$ a graph is returned and its marked volume is at most $nd$;
--   3. on every positive input, with probability at least $1-n^{-c}$ a collision is reported or the returned graph still contains a marked edge.
--
--   This is the high-degree half of the algorithm (Algorithm 6, cap_degrees).
--
--   Differences from the source:
--   - encoding: Õ(B) and 'the assigned error probability' → ∃ C, K (chosen after the error exponent c, before the vertex type and all parameters) with T ≤ C·B·(log₂ n)^K, n = |V| ≥ 2, and error ≤ n^{−c} for every c > 0; reason: the paper's conventions: Õ suppresses factors polynomial in log n and logarithms are base two (p.12); error probabilities are inverse polynomial in n (p.14)
--   - reading: the named procedure Algorithm 6 (cap_degrees) has the stated cost and guarantees → there is a T-query algorithm (QueryAlg, workspace Fin m) with that cost and those guarantees; reason: the procedure is a schema over black-box subroutines, so it is not one fixed object; the existence of a procedure with the printed cost and guarantees is what later proofs use (paper.md decision 4)
--   - reading: on a good negative execution it returns a graph of maximum degree at most d, hence marked volume at most nd → on every negative input, with probability ≥ 1 − n^{−c}, some G' is returned with vol(G', x) ≤ nd; reason: good executions have probability ≥ 1 − ε (proof, p.23); the degree bound is clause 1
--   - generalization: maximum degree at most d on a good negative execution → every returned graph G' satisfies G' ≤ G and has maximum degree ≤ d (on every input and outcome); reason: Algorithm 6 deletes every edge at the final high-degree set (lines 7–9) and outputs No on timeout; the proof of Theorem 1.1 (p.31) uses the degree bound on positive inputs too
--   - reading: degree bound d with 1 ≤ d ≤ n (type not stated) → d : ℝ; reason: the paper uses d as a real parameter in its cost exponents; every integer d (Theorem 1.1 takes d = ⌈n^{7/17}⌉) is an instance, so no case is dropped
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 4.2, p.22 (Algorithm 6 cap_degrees, p.22; proof pp.22–23)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_vol
import Definitions.Def_QGraphColl_eventProb

open QAlgorithms

namespace QGraphColl

/-- **Lemma 4.2** (Degree reduction; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.22). For `1 ≤ d ≤ n`, Algorithm 6 has query cost
`Õ(n^{3/4}/d^{1/4})`. On a good negative execution it returns a graph of maximum degree at most
`d`, hence marked volume at most `nd`. On a positive input it detects a collision or preserves
one, except with the assigned error.

**Formalization Note.**
* `Õ(B)` is `C · B · (log₂ n)^K` with `C, K` chosen after the error exponent `c` and before
  the vertex type and all parameters; "the assigned error" is `n^{-c}` for every `c > 0`
  (p.14: error probabilities are inverse polynomial in `n`), with `n = |V| ≥ 2`.
* Algorithm 6 (`cap_degrees`) is stated as the existence of a `T`-query algorithm with the
  printed cost. Its output is `none` ("Yes, a collision was detected") or `some G'`, a graph on
  the same labels.
* Every returned graph `G'` satisfies `G' ≤ G` (edge deletions) and has maximum degree `≤ d`:
  Algorithm 6 deletes every edge at the final high-degree set (lines 7–9). The proof of
  Theorem 1.1 (p.31) uses this degree bound on positive inputs too.
* On every negative input, with probability `≥ 1 − n^{-c}` a graph is returned and its marked
  volume is `≤ nd`; on every positive input, with probability `≥ 1 − n^{-c}` a collision is
  detected (`none`) or the returned graph still has a marked edge.
* The degree threshold `d` is real with `1 ≤ d ≤ n`. -/
theorem lemma_4_2 :
    ∀ c : ℝ, 0 < c → ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (d : ℝ), 1 ≤ d → d ≤ (Fintype.card V : ℝ) →
        ∃ T : ℕ, (T : ℝ) ≤ C * ((Fintype.card V : ℝ) ^ ((3 : ℝ) / 4) / d ^ ((1 : ℝ) / 4)) *
            Real.logb 2 (Fintype.card V : ℝ) ^ K ∧
          ∃ (m : ℕ) (A : QueryAlg V Bool (Fin m) T)
            (out : (V × Bool) × Fin m → Option (SimpleGraph V)),
            (∀ z G', out z = some G' → G' ≤ G ∧ ∀ v, (deg G' v : ℝ) ≤ d) ∧
            (∀ x : V → Bool, gc G x = false →
              eventProb A x out (fun o => ∃ G', o = some G' ∧
                (vol G' Finset.univ x : ℝ) ≤ (Fintype.card V : ℝ) * d)
                ≥ 1 - (Fintype.card V : ℝ) ^ (-c)) ∧
            (∀ x : V → Bool, gc G x = true →
              eventProb A x out (fun o => o = none ∨ ∃ G', o = some G' ∧ gc G' x = true)
                ≥ 1 - (Fintype.card V : ℝ) ^ (-c)) := by sorry

end QGraphColl
