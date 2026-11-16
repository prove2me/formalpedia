-- Prove2me | Theorems.Thm_QGraphColl_Supplement_theorem_6_1
-- name    : QGraphColl.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:33:28.04343+00:00
-- url     : https://prove2.me/theorems/62da8f9e-09e6-4a38-b0ee-e8f5f1c0961b
-- title:
--   Theorem 6.1 — $Q_2(\mathrm{gc}_{G_q})=\Omega(q\sqrt{\log q})$, hence an $n$-vertex graph with $Q_2(\mathrm{gc}_G)=\Omega(\sqrt{n\log n})$
-- statement:
--   Let $G_q$ be the Levi graph of points and nonvertical lines of $\mathbb F_q^2$, and let $Q_2(g)$ be the quantum query complexity of $g$ with error at most $1/3$ on every input. The theorem has two parts.
--
--   1. There are $c>0$ and $q_0$ such that for every finite field $\mathbb F_q$ with $q\ge q_0$, every quantum query algorithm that computes $\mathrm{gc}_{G_q}$ with error at most $1/3$ on every input $x\in\{0,1\}^{V(G_q)}$ makes
--   $$T\ \ge\ c\,q\sqrt{\log_2 q}$$
--   queries.
--   2. There are $c>0$ and $n_0$ such that for every $n\ge n_0$ there is a simple graph $G$ on $n$ vertices for which every quantum query algorithm computing $\mathrm{gc}_G$ with error at most $1/3$ on every input makes
--   $$T\ \ge\ c\sqrt{n\log_2 n}$$
--   queries.
--
--   Since $G_q$ has $n=2q^2$ vertices, the first part gives $\Omega(\sqrt{n\log n})$ on these graphs; the second extends it to every large $n$. The previous lower bound for arbitrary graphs was $\Omega(\sqrt n)$, from unstructured search, and the positive adversary method cannot exceed $O(\sqrt n)$ for graph collision because its positive certificates have size two. Part 2 rules out an $O(\sqrt n)$ algorithm for all graphs.
--
--   **Formalization Note** "Every algorithm" ranges over every `QueryAlg` with any finite workspace `Fin m` and any output map, with the standard Boolean oracle. $c$ and the thresholds are chosen before the field (resp. before $n$).
--
--   Differences from the source:
--   - encoding: Q₂(gc_{G_q}) = Ω(q√(log q)) → ∃ c > 0, q₀ such that every T-query algorithm computing gc_{G_q} with error ≤ 1/3 on every input has T ≥ c·q·√(log₂ q); reason: Q₂ is the least such T, so a lower bound on Q₂ is a lower bound on every such algorithm; Ω suppresses constants and the base of the logarithm only changes c
--   - encoding: sufficiently large prime powers q → every finite field K with Fintype.card K ≥ q₀; reason: G_q is defined from 𝔽_q, which exists exactly for prime powers q and is unique up to isomorphism
--   - encoding: for sufficiently large n, an n-vertex graph G with Q₂(gc_G) = Ω(√(n log n)) → ∃ c > 0, n₀, ∀ n ≥ n₀, ∃ G : SimpleGraph (Fin n) with every algorithm making T ≥ c·√(n·log₂ n) queries; reason: Ω read with its constant and threshold chosen before n
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Theorem 6.1, p.33 (informal version Theorem 1.2, p.3; G_q defined p.33; Q2 p.12)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_Supplement_leviGraph

open QAlgorithms

namespace QGraphColl.Supplement

/-- **Theorem 6.1** (A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou,
*Breaking the quantum barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026,
sha256 21da7ff0…), p.33; informal version Theorem 1.2, p.3): for all sufficiently large prime
powers `q`, `Q₂(gc_{G_q}) = Ω(q √(log q))`. Consequently, for sufficiently large values of `n`,
there is an `n`-vertex graph `G` with `Q₂(gc_G) = Ω(√(n log n))`.

**Formalization Note.**
* `Q₂(g) ≥ B` is stated over **every** algorithm: every `T`-query `QueryAlg` (any finite workspace
  `Fin m`, any output map) that computes `g` with error at most `1/3` on every input
  (`Finset.univ`) has `T ≥ B`.
* `Ω` is read as `∃ c > 0` and a threshold (`q₀`, resp. `n₀`), both chosen before the field,
  resp. before `n`. The two clauses carry their own constants.
* "Prime powers `q`" is every finite field `K` with `q = Fintype.card K`; `G_q` is
  `leviGraph K` on the vertex type `(K × K) ⊕ (K × K)` (points and nonvertical lines).
* Logarithms are base two (p.12); the base changes only `c`. The square roots cover the logarithm:
  `q·√(log q)` and `√(n·log n)` (rendered p.33). -/
theorem theorem_6_1 :
    (∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ,
      ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K], q₀ ≤ Fintype.card K →
        ∀ (T m : ℕ) (A : QueryAlg ((K × K) ⊕ (K × K)) Bool (Fin m) T)
          (out : (((K × K) ⊕ (K × K)) × Bool) × Fin m → Bool),
          A.ComputesWithError out Finset.univ (gc (leviGraph K)) (1 / 3) →
            c * (Fintype.card K : ℝ) * Real.sqrt (Real.logb 2 (Fintype.card K : ℝ)) ≤ T) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ G : SimpleGraph (Fin n),
        ∀ (T m : ℕ) (A : QueryAlg (Fin n) Bool (Fin m) T) (out : (Fin n × Bool) × Fin m → Bool),
          A.ComputesWithError out Finset.univ (gc G) (1 / 3) →
            c * Real.sqrt ((n : ℝ) * Real.logb 2 (n : ℝ)) ≤ T) := by sorry

end QGraphColl.Supplement
