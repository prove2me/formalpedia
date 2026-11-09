-- Prove2me | Theorems.Thm_QGraphColl_theorem_1_1
-- name    : QGraphColl.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:48.82185+00:00
-- url     : https://prove2.me/theorems/d7b66c1f-597a-4bf6-a9fc-5fd5d74ed1b8
-- title:
--   Theorem 1.1 — graph collision on every $n$-vertex graph with high probability using $\tilde O(n^{11/17})$ queries
-- statement:
--   For every $c>0$ there are constants $C,K>0$ such that for every $n\ge2$ and every simple graph $G$ on the vertex set $\{0,\dots,n-1\}$ there is a quantum query algorithm with
--   $$T\le C\,n^{11/17}(\log_2 n)^K$$
--   standard queries $|v,b\rangle\mapsto|v,b\oplus x_v\rangle$ which, on **every** input $x\in\{0,1\}^n$, outputs $\mathrm{gc}_G(x)$ — whether some edge of $G$ has both endpoints marked — with probability at least $1-n^{-c}$.
--
--   The previous best bound for arbitrary graphs was $O(n^{2/3})$ (Magniez, Santha, Szegedy), and $\Omega(n^{2/3})$ had been conjectured to be necessary for some graph families; $11/17<2/3$ refutes that conjecture.
--
--   **Formalization Note.** The algorithm is a `QueryAlg (Fin n) Bool (Fin m) T`: it may depend on $G$ (known in advance) and makes exactly $T$ queries on every input. All computation on the graph is free.
--
--   Differences from the source:
--   - reading: with high probability → error ≤ n^{−c} on every input, for every c > 0 (C, K depending on c); reason: the paper's convention: error probabilities are inverse polynomial in n (p.14), obtained by repeating O(log n) times (p.31)
--   - encoding: Õ(n^{11/17}) queries → ∃ C, K (after c, before n and G) with T ≤ C·n^{11/17}·(log₂ n)^K; reason: Õ suppresses factors polynomial in log n and logarithms are base two (p.12)
--   - encoding: any n-vertex graph → n ≥ 2 and G : SimpleGraph (Fin n); reason: for n ≤ 1 there is no edge and 0 queries suffice; n ≥ 2 keeps log₂ n > 0 ('for bounded n, query all input bits', p.31)
--   - reading: a quantum algorithm … using Õ(n^{11/17}) queries → a QueryAlg making exactly T queries on every input; reason: the paper's costs are worst-case fixed query limits (pp.14, 23)
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Theorem 1.1, p.3 (proof p.31; conventions p.12, p.14)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_gc

open QAlgorithms

namespace QGraphColl

/-- **Theorem 1.1** (A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.3): there is a quantum algorithm that solves the graph collision
problem on any `n`-vertex graph with high probability using `Õ(n^{11/17})` queries.

**Formalization Note.**
* "With high probability" is the paper's convention (pp.12, 14, 31: error probabilities are
  inverse polynomial in `n`, obtained by `O(log n)` repetitions): for every exponent `c > 0` the
  error is at most `n^{-c}` on **every** input `x ∈ {0,1}^n` (domain `Finset.univ`).
* `Õ(n^{11/17})` is `C · n^{11/17} · (log₂ n)^K` with `C, K` chosen after `c` and before `n`
  and `G` (logarithms are base two, p.12). `n ≥ 2` keeps `log₂ n > 0`; bounded `n` is handled by
  querying every bit (p.31).
* The algorithm is a `T`-query `QueryAlg` on the vertex set `Fin n` with standard queries
  `|v, b⟩ ↦ |v, b ⊕ x_v⟩` and any finite workspace `Fin m`; it may depend on `G` (the graph is
  known in advance) and makes exactly `T` queries on every input. -/
theorem theorem_1_1 :
    ∀ c : ℝ, 0 < c → ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ n : ℕ, 2 ≤ n → ∀ G : SimpleGraph (Fin n), ∃ T : ℕ,
        (T : ℝ) ≤ C * (n : ℝ) ^ ((11 : ℝ) / 17) * Real.logb 2 (n : ℝ) ^ K ∧
        ∃ (m : ℕ) (A : QueryAlg (Fin n) Bool (Fin m) T) (out : (Fin n × Bool) × Fin m → Bool),
          A.ComputesWithError out Finset.univ (gc G) ((n : ℝ) ^ (-c)) := by sorry

end QGraphColl
