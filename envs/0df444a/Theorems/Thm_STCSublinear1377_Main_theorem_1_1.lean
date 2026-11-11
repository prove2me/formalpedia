-- Prove2me | Theorems.Thm_STCSublinear1377_Main_theorem_1_1
-- name    : STCSublinear1377.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:36.802729+00:00
-- url     : https://prove2.me/theorems/0863d76d-f473-4fe8-970d-3719816ca553
-- title:
--   Theorem 1.1 — Full sublinear approximation, explicit form (3.19)
-- statement:
--   For each fixed confidence exponent $r>0$, there exist one uniform randomized polynomial-time algorithm and positive constants $C,C'$ such that the following holds for every connected simple unweighted graph $G$ with $n\ge2$ vertices. Put $m=|E(G)|$, $k=\operatorname{STC}(G)$ and $L=\log n$. Every random tape returns a spanning tree $T$ satisfying $c(G,T)\le8\sqrt{mn}$. With probability at least $1-n^{-r}$, the same output also satisfies both
--
--   $$\frac{c(G,T)}k\le C\min\left\{kL^5,\frac{\sqrt{mn}}k\right\},\qquad
--   \frac{c(G,T)}k\le C'n^{2/3}L^{5/3}.$$
--
--   The code, its time and random-bit polynomials, and the constants are chosen before the graph. The algorithm does not receive $k$, an optimum tree, a good partition or a low-load flow. This is the full detailed form of the headline $\widetilde O(n^{2/3})$ approximation, including its deterministic safeguard and arbitrarily polynomially small failure guarantee.
--
--   **Formalization Note** $k$ is computed mathematically as a finite attained minimum for analysis; it is not present in the machine input. Counting probability is over the uniform finite fair tape. On the stated domain $k\ge1$ and $L>0$; no supplied lower bound on $k$ or supplied inequality $m\le k(n-1)$ is assumed.
--
--   Differences from the source:
--   - encoding: an arbitrary finite graph → a binary adjacency table on Fin n; reason: every finite graph can be enumerated, and symmetry and absence of loops are checked explicitly
--   - encoding: polynomial-time computation → a uniform finite-work-alphabet TM2 evaluator with a polynomial step bound; reason: the evaluator is required to compute the encoded output on every encoded input, so time is tied to actual execution
--   - encoding: randomized polynomial time and probability at least 1 minus n to the minus r → one polynomial-length uniform fair tape and counting probability over all tapes; reason: every bit and evaluator step is charged and the common success event contains both source ratio bounds
--   - generalization: Theorem 1.1/3.10 state only the approximation ratio (the algorithm on p.15 returns the better of its candidate and the Proposition 1.2 tree) → an additional conclusion that every tape returns a spanning tree of congestion at most 8√(mn); reason: the extra clause implies the source statement, and the source's final comparison step supplies it
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Theorem 1.1 PDF/printed p.2; Theorem 3.10 and (3.19), PDF/printed p.15, including its last paragraph

import Definitions.Def_STCSublinear1377_Main_Machine
set_option autoImplicit false

namespace STCSublinear1377.Main

/-- Theorem 1.1 with all clauses of Theorem 3.10, equation (3.19), and its final probability
paragraph. The machine and constants precede every input graph. -/
theorem theorem_1_1 :
    ∀ r : ℝ, 0 < r →
    ∃ a : RandomGraphMachine, ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
      ∀ n : ℕ, 2 ≤ n → ∀ g : Table n, isInput g →
        (∀ tape : Fin (a.tapeLength n) → Bool,
          let out := a.output g tape
          let t := outputTable n out
          out.length = n * n ∧ spanning g t ∧
            (congestion g t : ℝ) ≤ 8 * Real.sqrt ((edgeCount g : ℝ) * n)) ∧
        tapeProbability a n (fun tape =>
          let t := outputTable n (a.output g tape)
          let k : ℝ := stc g
          let m : ℝ := edgeCount g
          let L := Real.log (n : ℝ)
          (congestion g t : ℝ) / k ≤ C * min (k * L ^ 5) (Real.sqrt (m * n) / k) ∧
          (congestion g t : ℝ) / k ≤
            C' * Real.rpow (n : ℝ) (2 / 3 : ℝ) * Real.rpow L (5 / 3 : ℝ))
          ≥ 1 - Real.rpow (n : ℝ) (-r) := by sorry

end STCSublinear1377.Main
