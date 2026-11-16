-- Prove2me | Theorems.Thm_TZLevelsADO_Supplement_theorem_7
-- name    : TZLevelsADO.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:22:23.213087+00:00
-- url     : https://prove2.me/theorems/a4aa4fd3-2d27-40c5-b3d1-820c80fa785a
-- title:
--   Theorem 7 ((t, s)-PSP-unweighted) — a $(k+2, k-1)$-approximation in $\tilde O(ms^{1/k} + (n+t)s^{2/k})$ time
-- statement:
--   Let $G$ range over connected unweighted undirected graphs (every edge has weight $1$) with $n$ vertices and $m$ edges, let $k \ge 1$ be an integer, let $I$ be a list of $t$ vertex pairs, and let $s \ge 1$ be such that some set $A$ of at most $s$ vertices hits every pair. Neither $A$ nor $s$ is given to the algorithm.
--
--   There is one program for the comparison–addition machine with the following property. For every $c \in \mathbb N$ there is a constant $C$ such that for every instance below:
--
--   1. on **every** outcome of the random coins, the program halts and its estimate $\hat d(u_j, v_j)$ for every pair satisfies $$d(u_j, v_j) \le \hat d(u_j, v_j) \le (k + 2)\, d(u_j, v_j) + (k - 1);$$;
--   2. with probability at least $1 - n^{-c}$, the program halts within $C\big((m+1)\,s^{1/k} + (n + t)\,s^{2/k}\big)(\lfloor\log_2 n\rfloor + 1)^C$ steps.
--
--   In the paper's words: there is an $\tilde O(ms^{1/k} + (n + t)s^{2/k})$-time $(k + 2, k - 1)$-approximation algorithm for $(t, s)$-PSP in unweighted undirected graphs. ST-shortest paths and multiple-source shortest paths are special cases (Corollaries 9 and 11).
--
--   **Formalization Note** The machine conventions are those of `RunsPSP`; the additive term $k - 1$ is absolute and the polylogarithmic factor is in $n$.
--
--   Differences from the source:
--   - reading: an algorithm in an unnamed model of computation → one program for the published comparison–addition RAM RealAPSP.Machine, with word bound (n + m + k + t + 2)^c, c fixed with the program; reason: the weights are reals and the algorithms only add and compare them; this is the machine of the mission’s Theorem 1, and every input integer (including t and the pair endpoints) fits in a word
--   - encoding: the pairs of I are given and an estimate d̂(u, v) is computed for every pair → RunsPSP: integer cells n, m, k, the edge endpoints, t, then the first and the second endpoints of the pairs; the estimate for the j-th pair in real cell routCell j of the halted state; reason: the paper fixes no layout; any fixed layout readable in O(m + t) steps describes the same problem
--   - reading: "running-time bounds hold with high probability" (p.7), Õ(·) suppressing polylog n → for every c ∈ ℕ there is C such that, with probability at least 1 − n^{−c}, the program halts within C·g·(⌊log₂ n⌋ + 1)^C steps; the program is fixed before c, and the approximation holds on every coin tape; reason: the conventional strongest reading of an unpinned "w.h.p.", the same as in the mission’s Theorem 1; the page prints no failure probability
--   - encoding: Õ(ms^{1/k} + (n + t)s^{2/k}) → C((m + 1)s^{1/k} + (n + t)s^{2/k})(⌊log₂ n⌋ + 1)^C, polylog in n; reason: m + 1 in place of m keeps the bound positive when m = 0 (n = 1); for connected graphs m ≥ n − 1, so no instance changes its order of growth
--   - generalization: k ≤ log n (footnote 1, p.1) → every k ≥ 1; reason: the source case k ≤ log n is an instance; for larger k an algorithm may run with k′ = max(1, ⌊log₂ n⌋) ≤ k levels, whose guarantee is at least as good and whose n^{1/k′} is at most 4
--   - generalization: an unweighted undirected graph, ℓ(x, y) = 1 (§2), connected → an edge list on Fin n with every weight equal to 1 (Unweighted) and Connected; parallel edges and loops allowed; reason: every connected unweighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - generalization: Definition 5: a set I of t pairs and a set A ⊆ V of s sources hitting every pair, A not given (footnote 3) → a list I of t = |I| pairs (repetitions allowed) and a natural number s ≥ 1 such that some A ⊆ V with |A| ≤ s hits every pair; neither A nor s is given to the program; reason: every source instance is one (|A| = s ≤ s); a larger s only weakens the bound. s ≥ 1 only excludes s = 0, where the printed bound s^{1/k} = 0 cannot be meant (it occurs only for t = 0)
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Theorem 7 ((t, s)-PSP-unweighted), p.4 (PDF p.5); Definition 5 and footnote 3, pp.3–4 (PDF pp.4–5); proof §8, pp.29–30 (PDF pp.30–31)

import Mathlib
import Definitions.Def_TZLevelsADO_Supplement_RunsPSP

namespace TZLevelsADO.Supplement

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Theorem 7 ((t, s)-PSP-unweighted), p.4 (PDF p.5), proved in §8,
pp.29–30 (PDF pp.30–31); Definition 5, pp.3–4, and footnote 3 ("The set A does not need to be given"):
"There is an Õ(ms^{1/k} + (n + t)s^{2/k})-time (k + 2, k − 1)-approximation algorithm for (t, s)-PSP
in unweighted undirected graphs."

**Formalization Note.**
* **Algorithm.** One program `Alg` for the published comparison–addition RAM (`RealAPSP.Machine`),
  fixed before `c` and before the instance; input layout, word size and output cells as in `RunsPSP`.
* **Approximation on every coin tape** ("our stretch bounds hold for every outcome of the sampling",
  p.7); **time with high probability**: for every `c ∈ ℕ` there is `C` such that, with probability at
  least `1 − n^{−c}`, the program halts within the time bound. `Õ(g)` is `C·g·(⌊log₂ n⌋+1)^C`.
* **Instances.** Every connected edge-list (multi)graph and every `k ≥ 1` (footnote 1, p.1, assumes
  `k ≤ log n`).
* **(t, s)-PSP.** A list `I` of `t = I.length` pairs and a number `s ≥ 1` such that some set of at
  most `s` vertices hits every pair; neither is given to the program. `|A| ≤ s` in place of
  `|A| = s` is more general; `s ≥ 1` excludes the degenerate bound `0^{1/k} = 0`. Unweighted: every
  edge has weight `1`. The `(k + 2, k − 1)`-approximation is
  `d(u, v) ≤ d̂(u, v) ≤ (k + 2)·d(u, v) + (k − 1)`. `m + 1` in place of `m` keeps the bound
  positive at `m = 0`. -/
theorem theorem_7 :
    ∃ Alg : RealAPSP.Program, ∀ c : ℕ, ∃ C : ℕ,
      ∀ (G : Graph) (k : ℕ) (I : List (Fin G.n × Fin G.n)) (s : ℕ),
        1 ≤ k → Unweighted G → G.Connected → 1 ≤ s →
        (∃ A : Finset (Fin G.n), A.card ≤ s ∧ ∀ p ∈ I, p.1 ∈ A ∨ p.2 ∈ A) →
        RunsPSP Alg G k I (IsApprox G ((k : ℝ) + 2) ((k : ℝ) - 1))
          (C * (((G.m : ℝ) + 1) * (s : ℝ) ^ ((1 : ℝ) / k) +
              ((G.n : ℝ) + I.length) * (s : ℝ) ^ ((2 : ℝ) / k)) *
            ((Nat.log 2 G.n : ℝ) + 1) ^ C)
          ((G.n : ℝ) ^ (-(c : ℝ))) := by sorry

end TZLevelsADO.Supplement
