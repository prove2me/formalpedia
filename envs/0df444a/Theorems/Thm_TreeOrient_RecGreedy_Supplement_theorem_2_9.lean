-- Prove2me | Theorems.Thm_TreeOrient_RecGreedy_Supplement_theorem_2_9
-- name    : TreeOrient.RecGreedy.Supplement.theorem_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:54:27.346645+00:00
-- url     : https://prove2.me/theorems/f15494b3-987d-43d7-8db5-70ab2d3a6ba1
-- title:
--   Theorem 2.9 — binary-search recursive greedy is an O(log k)-approximation in (n log B)^{O(log k)} steps
-- statement:
--   Fix $a\in\mathbb N$. Consider instances of submodular tree orienteering with $n$ vertices, root $r^*$, nonnegative integer costs $c$, budget $B$ and a monotone submodular reward $f$ with natural values satisfying $f(S)\le n^a$ for every $S$. For $2\le k\le n$ run Algorithm 2 as $RG\text{-}QP(r^*,\emptyset,B,\emptyset,d)$ with value bound $U=n^a$ and depth $d=2\lceil\log_2k\rceil$.
--
--   There is a constant $C>0$, depending only on $a$, such that for every such instance and $k$:
--
--   1. the algorithm returns an edge set $T$ of cost at most $B$ in which every vertex is reachable from $r^*$, and $T$ contains an $r^*$-rooted arborescence on the same vertices;
--   2. for every $r^*$-rooted arborescence $A$ of cost at most $B$ with at most $k$ vertices (root included),
--   $$f(V(A))\le C\,\log k\; f(V(T));$$
--   3. the algorithm takes at most $\bigl(n\log_2(B+2)\bigr)^{C\log k}$ steps.
--
--   This removes the pseudo-polynomial dependence on $B$ of Theorem 2.6 at the price of a constant factor in the ratio.
--
--   **Formalization Note** The algorithm is `alg29`, the published `rg I 1 (.bsearch (n ^ a))` at the published depth `dOf k`. The step count is the published model's and includes every binary-search probe.
--
--   Differences from the source:
--   - reading: "there is an $O(\log k)$-approximation algorithm" → the specified algorithm $RG\text{-}QP(r^*,\emptyset,B,\emptyset,2\lceil\log_2k\rceil)$ with $U=n^a$; reason: the theorem combines Proposition 2.7 and Lemma 2.8 about this algorithm; naming it rules out a vacuous existential.
--   - encoding: $f$ polynomially bounded in $n$ → $f(S)\le n^a$ for all $S$, with $C$ depending only on $a$; reason: the bound is the value range $U$ of the threshold guesses, as in the published goal.
--   - encoding: $f:2^V\to\mathbb R_+$ → natural-valued $f$ (the published model's oracle); reason: the threshold guesses $u\in[0,U]$ and Lemma 2.8's $\lceil U_1/(i-1)\rceil$ step use integer values.
--   - generalization: $k$ is the number of vertices of an optimal solution → any $k$ with $2\le k\le n$, compared with every feasible arborescence with at most $k$ vertices; reason: specializes to $k=|V(\mathrm{OPT})|$.
--   - encoding: $k\ge1$ → $k\ge2$; reason: at $k=1$, $\log k=0$ and an $O(\log k)$ ratio is undefined.
--   - generalization: costs satisfy the triangle inequality (without loss of generality, §1.3) → no triangle inequality; reason: the statement holds on every cost function.
--   - encoding: the returned arborescence → a returned edge set that is reachable from $r^*$, within budget, and contains an $r^*$-rooted arborescence on its vertices; reason: $T_1\cup T_2$ may share vertices, as in the published model.
--   - encoding: time $O(n\log B)^{O(\log k)}$ → at most $(n\log_2(B+2))^{C\log k}$ steps; reason: $B+2$ keeps the logarithm positive for $B=0,1$; the step count is the published model's.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, p. 8 (PDF 9), Theorem 2.9; Algorithm 2, p. 7 (PDF 8); Proposition 2.7 and Lemma 2.8, p. 8 (PDF 9)

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Supplement_TopLevel

namespace TreeOrient.RecGreedy.Supplement

/-- Theorem 2.9, p. 8 (PDF 9): Algorithm 2 with `U = n ^ a` is an `O(log k)`-approximation
running in `(n log B)^{O(log k)}` steps when `f ≤ n ^ a`. -/
theorem theorem_2_9 : ∀ a : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (I : Inst n) (k : ℕ),
      IsMonotone I.f →
      NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)) →
      (∀ S, I.f S ≤ n ^ a) → 2 ≤ k → k ≤ n →
      (∃ T, (alg29 I a k).1 = some T ∧ Feasible I.c I.root ∅ I.B T ∧
        (∃ A' : Edges n, A' ⊆ T ∧ IsArbo I.root A' ∧ verts I.root A' = verts I.root T) ∧
        ∀ A : Edges n, IsArbo I.root A → cost I.c A ≤ I.B → A.card + 1 ≤ k →
          (I.f (verts I.root A) : ℝ) ≤ C * Real.log k * (I.f (verts I.root T) : ℝ)) ∧
      ((alg29 I a k).2 : ℝ) ≤
        ((n : ℝ) * Real.logb 2 ((I.B : ℝ) + 2)) ^ (C * Real.log k) := by sorry

end TreeOrient.RecGreedy.Supplement
