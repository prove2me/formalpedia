-- Prove2me | Theorems.Thm_TZLevelsADO_theorem_1
-- name    : TZLevelsADO.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:50:17.496338+00:00
-- url     : https://prove2.me/theorems/42c2820f-1c76-4d2b-9834-29ec14ef9fd4
-- title:
--   Theorem 1 (ADO-weighted) — a $(\frac65 k+7)$-stretch distance oracle with $\tilde O(mn^{1/k})$ time and space and $\tilde O(n^{1/k})$ query time
-- statement:
--   Let $G$ range over connected undirected graphs with $n$ vertices, $m$ edges and positive real edge weights, and let $k \ge 1$ be an integer.
--
--   There are two programs for the comparison–addition machine, a preprocessing program and a query program, with the following property. For every $c \in \mathbb N$ there is a constant $C$ such that for every such $G$ and $k$:
--
--   1. on **every** outcome of the random coins, the preprocessing halts, and every query $\langle u, v\rangle$ halts with an answer $\hat d(u,v)$ satisfying
--   $$d(u, v) \le \hat d(u, v) \le \Big(\frac65 k + 7\Big)\, d(u, v);$$
--   2. with probability at least $1 - n^{-c}$, the preprocessing takes at most $C(m+1)\,n^{1/k}(\lfloor\log_2 n\rfloor + 1)^C$ steps, the data structure occupies at most $C(m+1)\,n^{1/k}(\lfloor\log_2 n\rfloor + 1)^C$ cells, and every query takes at most $C\,n^{1/k}(\lfloor\log_2 n\rfloor + 1)^C$ steps.
--
--   In the paper's words: there is an $\tilde O(mn^{1/k})$-time algorithm that constructs a $(\frac65 k + 7)$-stretch ADO for weighted undirected graphs, with $\tilde O(mn^{1/k})$ space and $\tilde O(n^{1/k})$ query time. It answers the paper's Question 1 and breaks the $2k - O(1)$ stretch barrier for oracles with $\tilde O(n^{1/k})$ query time on sparse graphs.
--
--   **Formalization Note** The data-structure semantics (input layout, the stored memory, the cleared coin cells, the query cells, the output cell and the space count) are those of `IsADO`.
--
--   Differences from the source:
--   - reading: an algorithm and data structure in an unnamed model of computation → programs for the published comparison–addition RAM RealAPSP.Machine, with word bound (n + m + k + 2)^c, c fixed with the program; reason: the weights are positive reals and the algorithms only add and compare them; the comparison–addition model is the standard model for real-weighted shortest paths, and every input integer fits in a word
--   - encoding: an ADO: a data structure answering queries ⟨u, v⟩, with its space → IsADO: the halted preprocessing memory; deterministic queries from it with coin cells cleared, u, v in two fixed cells and the answer in a fixed real cell; space = distinct cells stored to plus the 3 + 3m input cells; reason: the paper fixes no layout; clearing coins and counting input cells only exclude a query that uses free randomness or reads the graph for free
--   - reading: "time and space bounds hold with high probability", Õ(·) suppressing polylog n → for every c ∈ ℕ there is C such that with probability at least 1 − n^{−c} the time and space are at most C·g·(⌊log₂ n⌋ + 1)^C; the programs are fixed before c; reason: the conventional strongest reading of an unpinned "w.h.p."; the page prints no failure probability
--   - encoding: Õ(mn^{1/k}) → C(m + 1)n^{1/k}(⌊log₂ n⌋ + 1)^C; reason: m + 1 keeps the bound positive when m = 0 (n = 1); for connected graphs m ≥ n − 1
--   - generalization: k ≤ log n (footnote 1, p.1) → every k ≥ 1; reason: the source case k ≤ log n is an instance; for larger k an algorithm may run with k′ = max(1, ⌊log₂ n⌋) ≤ k levels, whose stretch is smaller and whose n^{1/k′} is at most 4
--   - generalization: an undirected graph G = (V, E) with positive real edge weights → an edge list on Fin n with positive real weights; parallel edges and loops allowed; reason: every weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - encoding: G is connected → Connected G: n ≥ 1 and every two vertices are joined by a walk; reason: a connected graph has a vertex; no instance of the source is excluded
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Theorem 1, p.1 (PDF p.2); restated and proved in §7, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_TZLevelsADO_IsADO

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Theorem 1 (ADO-weighted), p.1 (PDF p.2), restated and proved in
§7, p.26 (PDF p.27):
"There is an Õ(mn^{1/k})-time algorithm that constructs a (6/5 k+7)-stretch ADO for weighted
undirected graphs, with Õ(mn^{1/k}) space and Õ(n^{1/k}) query time."

**Formalization Note.**
* **Algorithm.** One preprocessing program `Pre` and one query program `Qry` on the published
  comparison–addition RAM (`RealAPSP.Machine`), fixed before everything else (see `IsADO` for the
  input layout, the stored memory, the query cells, the output cell and the space measure).
* **Stretch on every coin tape** ("our stretch bounds hold for every outcome of the sampling", p.7):
  preprocessing halts, and every query ⟨u, v⟩ halts with `d(u, v) ≤ d̂(u, v) ≤ (6/5·k + 7)·d(u, v)`.
* **Resources with high probability** ("our running-time and space bounds hold with high probability",
  p.7): for every `c ∈ ℕ` there is `C` such that, with probability at least `1 − n^{−c}`, preprocessing
  takes at most `C(m+1)n^{1/k}(⌊log₂ n⌋+1)^C` steps and space, and every query at most
  `C·n^{1/k}(⌊log₂ n⌋+1)^C` steps. `Õ(g)` is `C·g·(⌊log₂ n⌋+1)^C`; `m + 1` in place of `m` keeps the bound
  positive at `m = 0`.
* **Instances.** Every connected edge-list (multi)graph with positive real weights and every `k ≥ 1`
  (footnote 1, p.1, assumes `k ≤ log n`). -/
theorem theorem_1 :
    ∃ Pre Qry : RealAPSP.Program, ∀ c : ℕ, ∃ C : ℕ,
      ∀ (G : Graph) (k : ℕ), 1 ≤ k → G.PosWeights → G.Connected →
        IsADO Pre Qry G k ((6 / 5 : ℝ) * k + 7)
          (C * ((G.m : ℝ) + 1) * (G.n : ℝ) ^ ((1 : ℝ) / k) * ((Nat.log 2 G.n : ℝ) + 1) ^ C)
          (C * ((G.m : ℝ) + 1) * (G.n : ℝ) ^ ((1 : ℝ) / k) * ((Nat.log 2 G.n : ℝ) + 1) ^ C)
          (C * (G.n : ℝ) ^ ((1 : ℝ) / k) * ((Nat.log 2 G.n : ℝ) + 1) ^ C)
          ((G.n : ℝ) ^ (-(c : ℝ))) := by sorry

end TZLevelsADO
