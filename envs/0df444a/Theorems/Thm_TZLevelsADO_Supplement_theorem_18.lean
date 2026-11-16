-- Prove2me | Theorems.Thm_TZLevelsADO_Supplement_theorem_18
-- name    : TZLevelsADO.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:22:50.397463+00:00
-- url     : https://prove2.me/theorems/b71f7ed6-cb17-4416-8944-14eb23bdc0ac
-- title:
--   Theorem 18 (m-PSP-short paths) — a $k$-approximation in $\tilde O(mn^{1/k})$ time for pairs whose shortest path has at most 2 edges
-- statement:
--   Let $G$ range over connected undirected graphs with $n$ vertices, $m$ edges and positive real edge weights, let $k \ge 1$ be an integer, and let $I$ be a list of at most $m$ vertex pairs.
--
--   There is one program for the comparison–addition machine with the following property. For every $c \in \mathbb N$ there is a constant $C$ such that for every instance below:
--
--   1. on **every** outcome of the random coins, the program halts and its estimate $\hat d(u_j, v_j)$ for every pair satisfies $d(u_j, v_j) \le \hat d(u_j, v_j)$, and if moreover some shortest path from $u_j$ to $v_j$ has at most $2$ edges, then
--   $$\hat d(u_j, v_j) \le k\, d(u_j, v_j);$$;
--   2. with probability at least $1 - n^{-c}$, the program halts within $C(m+1)\,n^{1/k}(\lfloor\log_2 n\rfloor + 1)^C$ steps.
--
--   In the paper's words: there is an $\tilde O(mn^{1/k})$-time $k$-approximation algorithm for m-PSP in weighted undirected graphs, for queried pairs $\langle u, v\rangle$ whose shortest path $P(u, v)$ has at most $2$ edges. It answers a question of Kadria and Roditty on stretch exactly $k$ for pairs at distance $2$, and is within a factor $2$ of the 3SUM-based lower bound of Jin and Xu.
--
--   **Formalization Note** The machine conventions are those of `RunsPSP`. The guarantee is stated per pair, so one program serves inputs that mix short and long pairs.
--
--   Differences from the source:
--   - reading: an algorithm in an unnamed model of computation → one program for the published comparison–addition RAM RealAPSP.Machine, with word bound (n + m + k + t + 2)^c, c fixed with the program; reason: the weights are reals and the algorithms only add and compare them; this is the machine of the mission’s Theorem 1, and every input integer (including t and the pair endpoints) fits in a word
--   - encoding: the pairs of I are given and an estimate d̂(u, v) is computed for every pair → RunsPSP: integer cells n, m, k, the edge endpoints, t, then the first and the second endpoints of the pairs; the estimate for the j-th pair in real cell routCell j of the halted state; reason: the paper fixes no layout; any fixed layout readable in O(m + t) steps describes the same problem
--   - reading: "running-time bounds hold with high probability" (p.7), Õ(·) suppressing polylog n → for every c ∈ ℕ there is C such that, with probability at least 1 − n^{−c}, the program halts within C·g·(⌊log₂ n⌋ + 1)^C steps; the program is fixed before c, and the approximation holds on every coin tape; reason: the conventional strongest reading of an unpinned "w.h.p.", the same as in the mission’s Theorem 1; the page prints no failure probability
--   - encoding: Õ(mn^{1/k}) → C(m + 1)n^{1/k}(⌊log₂ n⌋ + 1)^C; reason: m + 1 in place of m keeps the bound positive when m = 0 (n = 1); for connected graphs m ≥ n − 1, so no instance changes its order of growth
--   - generalization: k ≤ log n (footnote 1, p.1) → every k ≥ 1; reason: the source case k ≤ log n is an instance; for larger k an algorithm may run with k′ = max(1, ⌊log₂ n⌋) ≤ k levels, whose guarantee is at least as good and whose n^{1/k′} is at most 4
--   - generalization: an undirected graph G = (V, E) with positive real edge weights, connected (§2) → an edge list on Fin n with positive real weights (PosWeights) and Connected (n ≥ 1 and every two vertices joined by a walk); parallel edges and loops allowed; reason: every connected weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - generalization: m-PSP: a set I ⊆ V × V of exactly m pairs → a list I of at most m pairs, repetitions allowed; reason: every set of m pairs is such a list; the time bound does not depend on the number of pairs below m
--   - generalization: a k-approximation for m-PSP "for queried pairs ⟨u, v⟩ whose shortest path P(u, v) has at most 2 edges" → one program for every list of at most m pairs: d(u, v) ≤ d̂(u, v) for every pair, and d̂(u, v) ≤ k·d(u, v) for every pair that has some shortest walk with at most 2 edges; reason: on inputs whose pairs all have such a shortest path (the proof in §6 assumes this of every pair of I) it is the source’s k-approximation; P(u, v) is an arbitrary fixed shortest path (§2), so "some shortest walk has at most 2 edges" covers every choice of P
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Theorem 18 (m-PSP-short paths), p.6 (PDF p.7); proof §6, pp.25–26 (PDF pp.26–27)

import Mathlib
import Definitions.Def_TZLevelsADO_Supplement_RunsPSP

namespace TZLevelsADO.Supplement

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Theorem 18 (m-PSP-short paths), p.6 (PDF p.7), proved in §6, pp.25–26
(PDF pp.26–27):
"There is an Õ(mn^{1/k})-time k-approximation algorithm for m-PSP in weighted undirected graphs, for
queried pairs ⟨u, v⟩ whose shortest path P(u, v) has at most 2 edges."

**Formalization Note.**
* **Algorithm.** One program `Alg` for the published comparison–addition RAM (`RealAPSP.Machine`),
  fixed before `c` and before the instance; input layout, word size and output cells as in `RunsPSP`.
* **Approximation on every coin tape** ("our stretch bounds hold for every outcome of the sampling",
  p.7); **time with high probability**: for every `c ∈ ℕ` there is `C` such that, with probability at
  least `1 − n^{−c}`, the program halts within the time bound. `Õ(g)` is `C·g·(⌊log₂ n⌋+1)^C`.
* **Instances.** Every connected edge-list (multi)graph and every `k ≥ 1` (footnote 1, p.1, assumes
  `k ≤ log n`).
* **m-PSP.** A list `I` of at most `m` pairs; positive real weights.
* **Short pairs, per pair.** Every output satisfies `d(u, v) ≤ d̂(u, v)`, and `d̂(u, v) ≤ k·d(u, v)`
  holds for every pair that has a shortest walk with at most `2` edges. On inputs whose pairs all have
  such a shortest path (the page's hypothesis) this is the page's `k`-approximation; `P(u, v)` is an
  arbitrary fixed shortest path (§2), so "some shortest walk has at most 2 edges" covers every choice. -/
theorem theorem_18 :
    ∃ Alg : RealAPSP.Program, ∀ c : ℕ, ∃ C : ℕ,
      ∀ (G : Graph) (k : ℕ) (I : List (Fin G.n × Fin G.n)),
        1 ≤ k → G.PosWeights → G.Connected → I.length ≤ G.m →
        RunsPSP Alg G k I
          (fun u v dhat => dist G u v ≤ dhat ∧
            ((∃ W, IsShortestWalk G u v W ∧ W.length ≤ 2) → dhat ≤ (k : ℝ) * dist G u v))
          (C * ((G.m : ℝ) + 1) * (G.n : ℝ) ^ ((1 : ℝ) / k) * ((Nat.log 2 G.n : ℝ) + 1) ^ C)
          ((G.n : ℝ) ^ (-(c : ℝ))) := by sorry

end TZLevelsADO.Supplement
