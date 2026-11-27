-- Prove2me | Theorems.Thm_TreeOrient_RecGreedy_Supplement_theorem_2_6
-- name    : TreeOrient.RecGreedy.Supplement.theorem_2_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:53:35.55396+00:00
-- url     : https://prove2.me/theorems/76ac5431-12ae-4b90-b578-b56f6d04f43d
-- title:
--   Theorem 2.6 (corrected: integer ratio ⌈log_{3/2} k⌉) — recursive greedy is a ⌈log_{3/2} k⌉-approximation for submodular tree orienteering in (nB)^{O(log k)} steps
-- statement:
--   Let an instance of submodular tree orienteering consist of $n$ vertices, a root $r^*$, nonnegative integer edge costs $c$, a budget $B$ and a monotone submodular reward $f$ with natural values. For $2\le k\le n$ let $d=\lceil\log_{3/2}k\rceil$ and run Algorithm 1 as $RG(r^*,\emptyset,B,\emptyset,d)$ (Remark 2.1).
--
--   There is an absolute constant $C>0$ such that, for every instance and every such $k$:
--
--   1. the algorithm returns an edge set $T$ of cost at most $B$ in which every vertex is reachable from $r^*$, and $T$ contains an $r^*$-rooted arborescence on the same vertices;
--   2. for every $r^*$-rooted arborescence $A$ of cost at most $B$ with at most $k$ vertices (root included),
--   $$f(V(A))\le \bigl\lceil\log_{3/2}k\bigr\rceil\; f(V(T));$$
--   3. the algorithm takes at most $\bigl(n\,(B+2)\bigr)^{C\log k}$ steps.
--
--   Taking $k$ to be the number of vertices of an optimal solution, this is the paper's $\log_{1.5}k$-approximation in time $O(nB)^{O(\log k)}$.
--
--   **Formalization Note** The algorithm is `alg26`, the published `rg I 1 .enum` at depth `d26 k`. The ratio is the integer depth itself: the analysis (Lemma 2.5) loses exactly a factor $d$, so no hidden constant enters the ratio. The step count is the published model's.
--
--   Differences from the source:
--   - reading: "there is a $(\log_{1.5}k)$-approximation algorithm" → the specified algorithm $RG(r^*,\emptyset,B,\emptyset,\lceil\log_{3/2}k\rceil)$; reason: the theorem follows from Remark 2.1, Proposition 2.4 and Lemma 2.5 about this algorithm; naming it rules out a vacuous existential.
--   - correction: ratio $\log_{1.5}k$ → $\lceil\log_{3/2}k\rceil$; reason: the paper derives the theorem from Remark 2.1 and Lemma 2.5, which give the factor $d$ for an integer depth $d\ge\log_{3/2}k$; this equals $\log_{1.5}k$ only when that is an integer, exceeds it by less than $1$ otherwise, and nothing in the paper gives the real value.
--   - generalization: $k$ is the number of vertices of an optimal solution → any $k$ with $2\le k\le n$, compared with every feasible arborescence with at most $k$ vertices; reason: specializes to $k=|V(\mathrm{OPT})|$.
--   - encoding: $k\ge1$ → $k\ge2$; reason: at $k=1$ the ratio $\log_{1.5}1=0$ is not an approximation ratio (the depth would be $0$).
--   - generalization: costs satisfy the triangle inequality (without loss of generality, §1.3) → no triangle inequality; reason: the statement holds on every cost function, in particular metric ones.
--   - generalization: $f$ polynomially bounded (§1.3) → no bound on $f$; reason: Algorithm 1 enumerates budgets, not values, so neither the ratio nor the step count uses the bound.
--   - encoding: $f:2^V\to\mathbb R_+$ → natural-valued $f$ (the published model's oracle); reason: Algorithm 1 only compares values of $f$, so scaling a rational-valued instance to integers changes neither its choices nor the ratio.
--   - encoding: the returned arborescence → a returned edge set that is reachable from $r^*$, within budget, and contains an $r^*$-rooted arborescence on its vertices; reason: $T_1\cup T_2$ may share vertices, as in the published model.
--   - encoding: time $O(nB)^{O(\log k)}$ → at most $(n(B+2))^{C\log k}$ steps with one absolute $C$; reason: $B+2$ keeps the base at least $2$ for $B=0$; the step count is the published model's.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, p. 7 (PDF 8), Theorem 2.6; Remark 2.1 and Proposition 2.4, p. 5 (PDF 6); Lemma 2.5, p. 6 (PDF 7)

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Supplement_TopLevel

namespace TreeOrient.RecGreedy.Supplement

/-- Theorem 2.6, p. 7 (PDF 8): Algorithm 1 at Remark 2.1's depth is a
`⌈log_{3/2} k⌉`-approximation running in `(n(B + 2))^{O(log k)}` steps. -/
theorem theorem_2_6 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (I : Inst n) (k : ℕ),
      IsMonotone I.f →
      NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)) →
      2 ≤ k → k ≤ n →
      (∃ T, (alg26 I k).1 = some T ∧ Feasible I.c I.root ∅ I.B T ∧
        (∃ A' : Edges n, A' ⊆ T ∧ IsArbo I.root A' ∧ verts I.root A' = verts I.root T) ∧
        ∀ A : Edges n, IsArbo I.root A → cost I.c A ≤ I.B → A.card + 1 ≤ k →
          (I.f (verts I.root A) : ℝ) ≤ (d26 k : ℝ) * (I.f (verts I.root T) : ℝ)) ∧
      ((alg26 I k).2 : ℝ) ≤ ((n : ℝ) * ((I.B : ℝ) + 2)) ^ (C * Real.log k) := by sorry

end TreeOrient.RecGreedy.Supplement
