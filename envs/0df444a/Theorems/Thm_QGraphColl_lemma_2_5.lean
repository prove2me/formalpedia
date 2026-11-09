-- Prove2me | Theorems.Thm_QGraphColl_lemma_2_5
-- name    : QGraphColl.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:17.760841+00:00
-- url     : https://prove2.me/theorems/ad39121b-47e6-4c5d-a883-a65cd1c094ad
-- title:
--   Lemma 2.5 — combining tests: the OR of tests with limits $q_i$ costs $\tilde O(\sqrt{\sum_i q_i^2})$
-- statement:
--   Let $n=|V|\ge2$ and fix a degree $\alpha>0$. Suppose $k\le n^\alpha$ tests are given, test $i$ having an edge list $G_i$ (a graph on the labels $V$), a stated bound $B_i$ (a condition on inputs) and a known query limit $q_i\le n^\alpha$: test $i$ is a $q_i$-query algorithm that, with error at most $1/3$, accepts every input positive for $G_i$ and rejects every input negative for $G_i$ satisfying $B_i$.
--
--   Then for every $c>0$ there are $C,K$ (depending only on $\alpha$ and $c$) and an algorithm with
--   $$T\le C\sqrt{\textstyle\sum_i q_i^2}\,(\log_2 n)^K$$
--   queries which, with error at most $n^{-c}$, accepts every input that is positive for some $G_i$ and rejects every input that is negative for all $G_i$ and satisfies all bounds $B_i$.
--
--   This is the variable-time OR used to combine the many collision tests of the algorithm.
--
--   Differences from the source:
--   - encoding: Õ(B) and 'the assigned error probability' → ∃ C, K (chosen after the error exponent c, before the vertex type and all parameters) with T ≤ C·B·(log₂ n)^K, n = |V| ≥ 2, and error ≤ n^{−c} for every c > 0; reason: the paper's conventions: Õ suppresses factors polynomial in log n and logarithms are base two (p.12); error probabilities are inverse polynomial in n (p.14)
--   - reading: polynomially many tests with known polynomially bounded query limits q_i → k ≤ n^α tests with q_i ≤ n^α, α > 0 fixed before C, K; reason: the meaning of 'polynomially many/bounded'
--   - reading: a test accepts every positive input for its own edge list and rejects negative inputs satisfying its stated bound → a q_i-query QueryAlg computing gc(G_i) on the domain {gc(G_i)} ∪ {¬gc(G_i) ∧ B_i}; reason: the bound restricts only the negative inputs (p.15, p.46)
--   - generalization: children with the assigned (inverse-polynomial) error → children with error at most 1/3; reason: the source's children have inverse-polynomially small error, in particular at most 1/3 once n is large; the proof reduces the children's error itself to δ ≤ 1/(4r) (p.46)
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 2.5, p.13 (restated with proof, p.46)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_eventProb

open QAlgorithms

namespace QGraphColl

/-- **Lemma 2.5** (Combining tests; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.13, restated p.46). Suppose polynomially many tests
have known polynomially bounded query limits `q_i`. Each accepts every positive input for its own
edge list and rejects negative inputs satisfying its stated bound. If all these bounds hold on a
global negative input, their OR can be tested in `Õ(√(∑_i q_i²))` queries, accepting every positive
global input.

**Formalization Note.**
* `Õ(B)` is `C · B · (log₂ n)^K` with `C, K` chosen after the error exponent `c` and before
  the vertex type and all parameters; "the assigned error probability" is `n^{-c}` for every `c > 0`
  (p.14: error probabilities are inverse polynomial in `n`), with `n = |V| ≥ 2`.
* "Polynomially many", "polynomially bounded": `k ≤ n^α` tests and `q_i ≤ n^α` for a degree
  `α > 0` fixed before `C, K`.
* Test `i` has edge list `Gs i` (a graph on the same labels) and stated bound `Bd i` (any predicate
  on inputs). It is a `q_i`-query algorithm computing `gc (Gs i)` with error `≤ 1/3` on its
  domain: all inputs positive for `Gs i`, and the inputs negative for `Gs i` that satisfy `Bd i`.
  Error `1/3` for the children is the general case (inverse-polynomial errors are smaller).
* The combined test computes "some `Gs i` has a marked edge" with error `≤ n^{-c}` on every input
  positive for some `Gs i`, and on every input negative for all `Gs i` that satisfies all bounds. -/
theorem lemma_2_5 :
    ∀ α : ℝ, 0 < α → ∀ c : ℝ, 0 < c → ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V →
      ∀ k : ℕ, (k : ℝ) ≤ (Fintype.card V : ℝ) ^ α →
      ∀ (Gs : Fin k → SimpleGraph V) (Bd : Fin k → (V → Bool) → Prop) (q : Fin k → ℕ),
        (∀ i, (q i : ℝ) ≤ (Fintype.card V : ℝ) ^ α) →
        (∀ i, ∃ (m : ℕ) (A : QueryAlg V Bool (Fin m) (q i)) (out : (V × Bool) × Fin m → Bool),
          A.ComputesWithError out
            (dom fun x => gc (Gs i) x = true ∨ (gc (Gs i) x = false ∧ Bd i x))
            (gc (Gs i)) (1 / 3)) →
        ∃ T : ℕ, (T : ℝ) ≤ C * Real.sqrt (∑ i, ((q i : ℝ)) ^ 2) *
            Real.logb 2 (Fintype.card V : ℝ) ^ K ∧
          ∃ (m : ℕ) (A : QueryAlg V Bool (Fin m) T) (out : (V × Bool) × Fin m → Bool),
            A.ComputesWithError out
              (dom fun x => (∃ i, gc (Gs i) x = true) ∨ (∀ i, gc (Gs i) x = false ∧ Bd i x))
              (fun x => decide (∃ i, gc (Gs i) x = true)) ((Fintype.card V : ℝ) ^ (-c)) := by sorry

end QGraphColl
