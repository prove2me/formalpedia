-- Prove2me | Theorems.Thm_TZLevelsADO_Supplement_theorem_6
-- name    : TZLevelsADO.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:21:42.095299+00:00
-- url     : https://prove2.me/theorems/1480fee5-5072-48c9-9848-3801b57a331a
-- title:
--   Theorem 6 ((t, s)-PSP-weighted) — a $(\frac65 k + 11)$-approximation in $\tilde O((m+t)s^{1/k})$ time
-- statement:
--   Let $G$ range over connected undirected graphs with $n$ vertices, $m$ edges and positive real edge weights, let $k \ge 1$ be an integer, let $I$ be a list of $t$ vertex pairs, and let $s \ge 1$ be such that some set $A$ of at most $s$ vertices hits every pair ($A \cap \{u, v\} \ne \emptyset$ for every $\langle u, v\rangle \in I$). Neither $A$ nor $s$ is given to the algorithm.
--
--   There is one program for the comparison–addition machine with the following property. For every $c \in \mathbb N$ there is a constant $C$ such that for every instance below:
--
--   1. on **every** outcome of the random coins, the program halts and its estimate $\hat d(u_j, v_j)$ for every pair satisfies $$d(u_j, v_j) \le \hat d(u_j, v_j) \le \Big(\frac65 k + 11\Big)\, d(u_j, v_j);$$;
--   2. with probability at least $1 - n^{-c}$, the program halts within $C(m + t + 1)\,s^{1/k}(\lfloor\log_2 n\rfloor + 1)^C$ steps.
--
--   In the paper's words: there is an $\tilde O((m + t)s^{1/k})$-time $(\frac65 k + 11)$-approximation algorithm for $(t, s)$-PSP in weighted undirected graphs. The factor $n^{1/k}$ of Theorem 3 becomes $s^{1/k}$; ST-shortest paths and multiple-source shortest paths are special cases (Corollaries 8 and 10).
--
--   **Formalization Note** The machine conventions are those of `RunsPSP`; the polylogarithmic factor is in $n$.
--
--   Differences from the source:
--   - reading: an algorithm in an unnamed model of computation → one program for the published comparison–addition RAM RealAPSP.Machine, with word bound (n + m + k + t + 2)^c, c fixed with the program; reason: the weights are reals and the algorithms only add and compare them; this is the machine of the mission’s Theorem 1, and every input integer (including t and the pair endpoints) fits in a word
--   - encoding: the pairs of I are given and an estimate d̂(u, v) is computed for every pair → RunsPSP: integer cells n, m, k, the edge endpoints, t, then the first and the second endpoints of the pairs; the estimate for the j-th pair in real cell routCell j of the halted state; reason: the paper fixes no layout; any fixed layout readable in O(m + t) steps describes the same problem
--   - reading: "running-time bounds hold with high probability" (p.7), Õ(·) suppressing polylog n → for every c ∈ ℕ there is C such that, with probability at least 1 − n^{−c}, the program halts within C·g·(⌊log₂ n⌋ + 1)^C steps; the program is fixed before c, and the approximation holds on every coin tape; reason: the conventional strongest reading of an unpinned "w.h.p.", the same as in the mission’s Theorem 1; the page prints no failure probability
--   - encoding: Õ((m + t)s^{1/k}) → C(m + t + 1)s^{1/k}(⌊log₂ n⌋ + 1)^C, polylog in n; reason: m + 1 in place of m keeps the bound positive when m = 0 (n = 1); for connected graphs m ≥ n − 1, so no instance changes its order of growth
--   - generalization: k ≤ log n (footnote 1, p.1) → every k ≥ 1; reason: the source case k ≤ log n is an instance; for larger k an algorithm may run with k′ = max(1, ⌊log₂ n⌋) ≤ k levels, whose guarantee is at least as good and whose n^{1/k′} is at most 4
--   - generalization: an undirected graph G = (V, E) with positive real edge weights, connected (§2) → an edge list on Fin n with positive real weights (PosWeights) and Connected (n ≥ 1 and every two vertices joined by a walk); parallel edges and loops allowed; reason: every connected weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - generalization: Definition 5: a set I of t pairs and a set A ⊆ V of s sources hitting every pair, A not given (footnote 3) → a list I of t = |I| pairs (repetitions allowed) and a natural number s ≥ 1 such that some A ⊆ V with |A| ≤ s hits every pair; neither A nor s is given to the program; reason: every source instance is one (|A| = s ≤ s); a larger s only weakens the bound. s ≥ 1 only excludes s = 0, where the printed bound s^{1/k} = 0 cannot be meant (it occurs only for t = 0)
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Theorem 6 ((t, s)-PSP-weighted), p.4 (PDF p.5); Definition 5 and footnote 3, pp.3–4 (PDF pp.4–5); proof §8, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_TZLevelsADO_Supplement_RunsPSP

namespace TZLevelsADO.Supplement

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Theorem 6 ((t, s)-PSP-weighted), p.4 (PDF p.5), proved in §8, p.30
(PDF p.31); Definition 5, pp.3–4: "The input is a set I of t prescribed pairs such that there exists a
set A ⊆ V of s sources that hits every pair, that is, A ∩ {u, v} ≠ ∅ for every ⟨u, v⟩ ∈ I." Footnote 3:
"The set A does not need to be given."
"There is an Õ((m + t)s^{1/k})-time (6/5 k + 11)-approximation algorithm for (t, s)-PSP in weighted
undirected graphs."

**Formalization Note.**
* **Algorithm.** One program `Alg` for the published comparison–addition RAM (`RealAPSP.Machine`),
  fixed before `c` and before the instance; input layout, word size and output cells as in `RunsPSP`.
* **Approximation on every coin tape** ("our stretch bounds hold for every outcome of the sampling",
  p.7); **time with high probability**: for every `c ∈ ℕ` there is `C` such that, with probability at
  least `1 − n^{−c}`, the program halts within the time bound. `Õ(g)` is `C·g·(⌊log₂ n⌋+1)^C`.
* **Instances.** Every connected edge-list (multi)graph and every `k ≥ 1` (footnote 1, p.1, assumes
  `k ≤ log n`).
* **(t, s)-PSP.** A list `I` of `t = I.length` pairs and a number `s ≥ 1` such that some set of at
  most `s` vertices hits every pair. Neither the set nor `s` is given to the program; `s` occurs only
  in the time bound. `|A| ≤ s` in place of `|A| = s` is more general (the bound grows with `s`);
  `s ≥ 1` excludes the degenerate bound `0^{1/k} = 0`. Positive real weights; the polylog factor is in
  `n`. `m + t + 1` in place of `m + t` keeps the bound positive at `m = t = 0`. -/
theorem theorem_6 :
    ∃ Alg : RealAPSP.Program, ∀ c : ℕ, ∃ C : ℕ,
      ∀ (G : Graph) (k : ℕ) (I : List (Fin G.n × Fin G.n)) (s : ℕ),
        1 ≤ k → G.PosWeights → G.Connected → 1 ≤ s →
        (∃ A : Finset (Fin G.n), A.card ≤ s ∧ ∀ p ∈ I, p.1 ∈ A ∨ p.2 ∈ A) →
        RunsPSP Alg G k I (IsApprox G ((6 / 5 : ℝ) * k + 11) 0)
          (C * ((G.m : ℝ) + I.length + 1) * (s : ℝ) ^ ((1 : ℝ) / k) * ((Nat.log 2 G.n : ℝ) + 1) ^ C)
          ((G.n : ℝ) ^ (-(c : ℝ))) := by sorry

end TZLevelsADO.Supplement
