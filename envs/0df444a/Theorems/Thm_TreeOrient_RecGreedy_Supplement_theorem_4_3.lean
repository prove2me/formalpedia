-- Prove2me | Theorems.Thm_TreeOrient_RecGreedy_Supplement_theorem_4_3
-- name    : TreeOrient.RecGreedy.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:55:57.335698+00:00
-- url     : https://prove2.me/theorems/6cc603e7-5f13-413d-9717-9b3f76a8b9f7
-- title:
--   Theorem 4.3 (corrected: RG-DC guesses from 0, D₁(v) kept) — RG-DC is an O(log k)-approximation for STO with length constraints in (nBL²)^{O(log k)} steps
-- statement:
--   Consider submodular tree orienteering with length constraints: $n$ vertices, a root $r^*$, nonnegative integer edge costs $c$ and lengths $\ell$, a budget $B$, a length bound $L$, and a monotone submodular reward $f$ with natural values. For an $r^*$-rooted arborescence $A$ write $l_A(v)$ for the length of the $r^*$–$v$ path; $A$ is feasible if $c(A)\le B$ and $\sum_{v}l_A(v)\le L$. For $2\le k\le n$ run Algorithm 3 as $RG\text{-}DC(r^*,0,\emptyset,\cdot,B,L,\emptyset,d)$ with $d=2\lceil\log_2k\rceil$.
--
--   There is an absolute constant $C>0$ such that for every instance and every such $k$:
--
--   1. the algorithm returns an edge set $T$ of cost at most $B$ in which every vertex is reachable from $r^*$, and $T$ contains an $r^*$-rooted arborescence on the same vertices whose path lengths sum to at most $L$;
--   2. for every feasible arborescence $A$ with at most $k$ vertices (root included),
--   $$f(V(A))\le C\,\log k\;f(V(T));$$
--   3. the algorithm takes at most $\bigl(n\,(B+2)\,(L+2)^2\bigr)^{C\log k}$ steps.
--
--   The result is pseudo-polynomial in both $B$ and $L$; Theorem 1.2 improves the dependence on $B$ and the ratio.
--
--   **Formalization Note** The algorithm is `alg43`, i.e. `rgdc I 1 .enum` at the published depth `dOf k`, defined in `TreeOrient.RecGreedy.Supplement.LengthModel`; its step count charges every call, guess, sub-call and evaluation.
--
--   Differences from the source:
--   - reading: "there is an $O(\log k)$-approximation algorithm" → the specified algorithm $RG\text{-}DC(r^*,0,\emptyset,\cdot,B,L,\emptyset,2\lceil\log_2k\rceil)$; reason: the theorem combines Proposition 4.1 and Lemma 4.2 about this algorithm; naming it rules out a vacuous existential.
--   - correction: Algorithm 3 guesses $B_1$, $L_1$, $d_1$ from $1$ → from $0$, with guesses $d_1>D(w)$ skipped, and $D_1(v)=\min\{d_1,D(v)\}$ for every separator $v\in Y$ (printed lines 16–17 forget $D(v)$ when $v\notin S$); reason: the counterexamples recorded at Lemma 4.2: zero-cost edges with $B=0$ defeat the printed ranges at the top level as well, and the forgotten bound lets a subcall return a longer path to the separator than the parent's guess $d_1$, which the proof's step (8) needs.
--   - generalization: $k$ is the number of vertices of an optimal solution → any $k$ with $2\le k\le n$, compared with every feasible arborescence with at most $k$ vertices; reason: specializes to $k=|V(\mathrm{OPT})|$.
--   - encoding: $k\ge1$ → $k\ge2$; reason: at $k=1$, $\log k=0$ and an $O(\log k)$ ratio is undefined.
--   - generalization: triangle inequality (without loss of generality, §1.3) → not assumed; reason: the statement holds on every cost function.
--   - generalization: $f$ polynomially bounded (§1.3) → no bound on $f$; reason: Algorithm 3 enumerates budgets and lengths, not values.
--   - encoding: $f:2^V\to\mathbb R_+$, $\ell:E\to\mathbb Z_+$ → natural-valued $f$ and lengths (zero allowed); reason: the published model's oracle; enumeration only compares values of $f$, so rational instances scale to integer ones.
--   - encoding: the returned arborescence → a returned edge set that is reachable, within budget, and contains an arborescence on its vertices with length sum at most $L$; reason: $T_1\cup T_2$ may share vertices.
--   - encoding: time $O(nBL^2)^{O(\log k)}$ → at most $(n(B+2)(L+2)^2)^{C\log k}$ steps; reason: $B+2$ and $L+2$ avoid degenerate bases at $B=0$ or $L=0$.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, p. 13 (PDF 14), Theorem 4.3; §4.1, p. 10 (PDF 11); Proposition 4.1 and Lemma 4.2, p. 11 (PDF 12); Algorithm 3, p. 12 (PDF 13)

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Supplement_LengthModel

namespace TreeOrient.RecGreedy.Supplement

/-- Theorem 4.3, p. 13 (PDF 14): Algorithm 3 at depth `dOf k` is an `O(log k)`-approximation
for STO with length constraints running in `(n(B + 2)(L + 2)²)^{O(log k)}` steps. -/
theorem theorem_4_3 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (I : LInst n) (k : ℕ),
      IsMonotone I.f →
      NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)) →
      2 ≤ k → k ≤ n →
      (∃ T, (alg43 I k).1 = some T ∧
        FeasibleDC I I.root 0 ∅ (fun _ => 0) I.B I.L T ∧
        ∀ A : Edges n, IsArbo I.root A → cost I.c A ≤ I.B →
          lenSum I.len 0 I.root A ≤ I.L → A.card + 1 ≤ k →
          (I.f (verts I.root A) : ℝ) ≤ C * Real.log k * (I.f (verts I.root T) : ℝ)) ∧
      ((alg43 I k).2 : ℝ) ≤
        ((n : ℝ) * ((I.B : ℝ) + 2) * ((I.L : ℝ) + 2) ^ 2) ^ (C * Real.log k) := by sorry

end TreeOrient.RecGreedy.Supplement
