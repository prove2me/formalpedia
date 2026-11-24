-- Prove2me | Theorems.Thm_TreeOrient_RecGreedy_Supplement_theorem_1_2
-- name    : TreeOrient.RecGreedy.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:56:32.552968+00:00
-- url     : https://prove2.me/theorems/e37dbf7f-57a2-43c3-88bb-74db2ae48831
-- title:
--   Theorem 1.2 (corrected: RG-DC guesses from 0, D₁(v) kept) — grouped RG-DC is an O(log k/log log k)-approximation for STO with length constraints in quasi-polynomial time
-- statement:
--   Fix $\varepsilon>0$ and $a\in\mathbb N$. Consider submodular tree orienteering with length constraints: $n$ vertices, a root $r^*$, nonnegative integer edge costs $c$ and lengths $\ell$, a budget $B$, a length bound $L\le n^a$, and a monotone submodular reward $f$ with natural values and $f(S)\le n^a$ for all $S$. An $r^*$-rooted arborescence $A$ is feasible if $c(A)\le B$ and $\sum_v l_A(v)\le L$, where $l_A(v)$ is the length of the $r^*$–$v$ path in $A$.
--
--   For $3\le k\le n$ run the algorithm of §4.1.1: Algorithm 3 with $s=\max\{1,\lceil\varepsilon\log_2\log_2k\rceil\}$ levels guessed at once, the cost budgets found by binary search over value thresholds $u\in[0,n^a]$, depth $\lceil d/s\rceil$ with $d=2\lceil\log_2k\rceil$, called from $(r^*,k_r=0,Y=\emptyset)$.
--
--   There is a constant $C>0$, depending only on $\varepsilon$ and $a$, such that for every such instance and $k$:
--
--   1. the algorithm returns an edge set $T$ of cost at most $B$ in which every vertex is reachable from $r^*$, and $T$ contains an $r^*$-rooted arborescence on the same vertices whose path lengths sum to at most $L$;
--   2. for every feasible arborescence $A$ with at most $k$ vertices (root included),
--   $$f(V(A))\le C\,\frac{\log k}{\log\log k}\;f(V(T));$$
--   3. the algorithm takes at most
--   $$\bigl(n\,(L+2)\,\log_2(B+2)\bigr)^{C(\log k)^{1+\varepsilon}}$$
--   steps.
--
--   This is the length-constrained counterpart of Theorem 1.1, and the result the paper applies to single-source buy-at-bulk and priority Steiner tree.
--
--   **Formalization Note** The algorithm is `stoDCAlg I a ε k`, the grouped `rgdc` of `TreeOrient.RecGreedy.Supplement.LengthModel`. Grouped levels assign cost and length budgets leaf by leaf, and grouped depth one searches every arborescence within the $(3/2)^s$ cap, as in the published Theorem 1.1. The parameters $s$, $d$ and $\lceil d/s\rceil$ are the published `sOf`, `dOf`, `depthOf`.
--
--   Differences from the source:
--   - reading: "runs in quasi-polynomial time" → at most $(n(L+2)\log_2(B+2))^{C(\log k)^{1+\varepsilon}}$ steps; reason: this is the bound $(nL\log B)^{O(\log^{1+\varepsilon}k)}$ that §4.1.1 proves for the algorithm ("This completes the proof of Theorem 1.2"); $B+2$ and $L+2$ avoid degenerate bases.
--   - reading: "there is an $O(\log k/\log\log k)$-approximation algorithm" → the specified grouped algorithm of §4.1.1; reason: §4.1.1 proves the theorem for this algorithm; naming it rules out a vacuous existential.
--   - correction: Algorithm 3 guesses $B_1$, $L_1$, $d_1$ from $1$ → from $0$, with guesses $d_1>D(w)$ skipped, and $D_1(v)=\min\{d_1,D(v)\}$ for every separator $v\in Y$ (printed lines 16–17 forget $D(v)$ when $v\notin S$); reason: the counterexamples recorded at Lemma 4.2 (zero-cost edges with $B=0$; a forgotten bound $D(v)$ breaking the proof's step (8)).
--   - encoding: $f$ polynomially bounded → $f(S)\le n^a$ for all $S$, with $C$ depending only on $\varepsilon$ and $a$; reason: the bound is the range $U$ of the value thresholds, as in the published Theorem 1.1.
--   - generalization: lengths polynomially bounded (§1.1) and $L$ polynomially bounded (§4.1.1) → only $L\le n^a$; reason: only $L$ enters the guesses and the time bound; an edge longer than $L$ cannot lie on a feasible path, so bounding $L$ also bounds every usable length.
--   - encoding: $f:2^V\to\mathbb R_+$, $\ell:E\to\mathbb Z_+$ → natural-valued $f$ and lengths (zero allowed); reason: the threshold guesses use integer values, as in the published model.
--   - generalization: $k$ is the number of vertices of an optimal solution → any $k$ with $3\le k\le n$, compared with every feasible arborescence with at most $k$ vertices; reason: specializes to $k=|V(\mathrm{OPT})|$.
--   - encoding: $k\ge1$ → $k\ge3$; reason: $\log\log k\le0$ for $k\le2$, so the ratio $\log k/\log\log k$ is undefined there.
--   - generalization: triangle inequality (without loss of generality, §1.3) → not assumed; reason: the statement holds on every cost function.
--   - encoding: "in one level guess all quantities in $s$ levels of Algorithm 3" → budgets assigned leaf by leaf, intermediate size checks omitted, grouped depth one searching every arborescence within the cap; reason: the same encoding as the published grouped algorithm of Theorem 1.1; budget splits over the leaves are the same set of guesses.
--   - encoding: the returned arborescence → a returned edge set that is reachable, within budget, and contains an arborescence on its vertices with length sum at most $L$; reason: unions of subtrees may share vertices.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, p. 3 (PDF 4), Theorem 1.2; §4.1.1, p. 13 (PDF 14) (proof and running time); §4.1, p. 10 (PDF 11); Algorithm 3, p. 12 (PDF 13)

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Supplement_LengthModel

namespace TreeOrient.RecGreedy.Supplement

/-- Theorem 1.2, p. 3 (PDF 4), with the running time of §4.1.1, p. 13 (PDF 14): the grouped,
binary-searched RG-DC is an `O(log k / log log k)`-approximation for STO with length
constraints running in `(nL log B)^{O(log^{1+ε} k)}` steps. -/
theorem theorem_1_2 : ∀ ε : ℝ, 0 < ε → ∀ a : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (I : LInst n) (k : ℕ),
      IsMonotone I.f →
      NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)) →
      (∀ S, I.f S ≤ n ^ a) → I.L ≤ n ^ a → 3 ≤ k → k ≤ n →
      (∃ T, (stoDCAlg I a ε k).1 = some T ∧
        FeasibleDC I I.root 0 ∅ (fun _ => 0) I.B I.L T ∧
        ∀ A : Edges n, IsArbo I.root A → cost I.c A ≤ I.B →
          lenSum I.len 0 I.root A ≤ I.L → A.card + 1 ≤ k →
          (I.f (verts I.root A) : ℝ) ≤
            C * (Real.log k / Real.log (Real.log k)) * (I.f (verts I.root T) : ℝ)) ∧
      ((stoDCAlg I a ε k).2 : ℝ) ≤
        ((n : ℝ) * ((I.L : ℝ) + 2) * Real.logb 2 ((I.B : ℝ) + 2)) ^
          (C * Real.log k ^ (1 + ε)) := by sorry

end TreeOrient.RecGreedy.Supplement
