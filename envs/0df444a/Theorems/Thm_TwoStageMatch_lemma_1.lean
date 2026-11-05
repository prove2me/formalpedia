-- Prove2me | Theorems.Thm_TwoStageMatch_lemma_1
-- name    : TwoStageMatch.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:15.17092+00:00
-- url     : https://prove2.me/theorems/326aff15-e3d2-416f-9636-a9bbae0ac476
-- title:
--   Lemma 1 — structural decomposition (corrected: supply-free components)
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be differentiable, monotone (non-decreasing) and strictly convex. Suppose all weights are positive, let $x^*$ be an optimal solution of $\mathscr P^g$, and write $y^*_j=\sum_{i\in N(j)}x^*_{ij}$. Let $G'=(D_1,S,E')$ with $E'=\{(i,j):x^*_{ij}>0\}$, let $S^{(0)}=\{j: y^*_j=1\}$, $D^{(0)}=\{i\in D_1:\exists j\in S^{(0)},x^*_{ij}>0\}$, and let the remaining levels be the connected components of $G'[D_1\setminus D^{(0)},S\setminus S^{(0)}]$, with slacks $c^{(l)}$ ($c^{(0)}=0$; a component without supply vertices has slack $0$). Then:
--
--   1. (Uniformity) for every level $l$ and every supply $j\in S^{(l)}$, $w_j(1-y^*_j)=c^{(l)}$; in particular all supplies of a level have the same value $w_j(1-y^*_j)$, and it is $0$ on level $0$.
--   2. (Monotonicity) for every edge $(i,j)\in E$ with $i\in D^{(l)}$ and $j\in S^{(l')}$, $c^{(l')}\le c^{(l)}$; equivalently, there is no edge of $E$ between $D^{(l)}$ and $S^{(l')}$ if $c^{(l)}<c^{(l')}$.
--   3. (Saturation) every $i\in D^{(l)}$, for a component $l$ containing a supply vertex, is fully matched: $\sum_{j\in N(i)}x^*_{ij}=1$.
--   4. (Supply-free components) a component that contains no supply vertex consists of a single demand vertex $i$, and every supply $j$ with $(i,j)\in E$ lies in $S^{(0)}$.
--
--   The printed lemma states saturation for every component $l\ge 1$. That fails for a component without supply vertices: take $D_1=\{a,b\}$, $S=\{s\}$, $w_s=1$, $E=\{(a,s),(b,s)\}$; then $x^*=(x^*_{as},x^*_{bs})=(1,0)$ is optimal for every admissible $g$ (for instance $g=\exp$), $S^{(0)}=\{s\}$, $D^{(0)}=\{a\}$, and $(\{b\},\emptyset)$ is a component with $\sum_j x^*_{bj}=0$. Clauses 3 and 4 are the corrected statement; the proof of Theorem 1 goes through with $\alpha_b=c=0$ on such a vertex.
--
--   This decomposition is the structural input to the dual-fitting proof of Theorem 1: it fixes the demand duals $\alpha_i=c^{(l)}$ and gives Type I feasibility (6).
--
--   Differences from the source:
--   - correction: (iii) saturation for every component l ∈ [1 : L], with c(l) defined through a supply vertex of the component → saturation for components that contain a supply vertex, plus clause 4 (a supply-free component is one demand vertex whose E-neighbours all lie in S⁽⁰⁾), with c := 0 on such a component; reason: counterexample satisfying every assumption: D₁ = {a, b}, S = {s}, w_s = 1, E = {(a, s), (b, s)}, g = exp; x* = (1, 0) is optimal and ({b}, ∅) is a component with Σ_j x*_bj = 0 ≠ 1
--   - correction: the L ≥ 1 connected components of G′[D₁ \ D⁽⁰⁾, S \ S⁽⁰⁾] → any number L ≥ 0 of components (no claim that L ≥ 1); reason: counterexample: D₁ = {a}, S = {s}, one edge, w_s = 1; x* = 1 is optimal and the induced subgraph is empty, so L = 0
--   - encoding: 𝒫^g and its optimal solution, with 1/w_j in the objective → hypothesis w_j > 0 for every supply j; reason: the paper's 𝒫^g divides by w_j and is undefined when some w_j = 0; the hypothesis excludes only that undefined case
--   - reading: the optimal solution x* of 𝒫^g → every optimal solution x*; reason: 𝒫^g need not have a unique minimizer in x (only the loads y* are pinned down); the claim is made for each
--   - encoding: uniformity ∀ l, j, j′ ∈ S⁽ˡ⁾: w_j(1 − y*_j) = w_j′(1 − y*_j′) ≜ c⁽ˡ⁾; monotonicity: no edge of E between D⁽ˡ⁾ and S⁽ˡ′⁾ if c⁽ˡ⁾ < c⁽ˡ′⁾ → every supply's value w_j(1 − y*_j) equals the slack of its level (c⁽ˡ⁾ defined through a chosen supply vertex); for every edge (i, j) ∈ E, c(level j) ≤ c(level i); levels as Option of the connected components; reason: equivalent formulations (contrapositive of monotonicity, stated for every pair of levels including l = l′); same instances
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, Lemma 1, pp.13–14 (restated p.ec4, proof pp.ec5–ec6)

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1
import Definitions.Def_TwoStageMatch_Decomposition

namespace TwoStageMatch

/-- **Lemma 1 (Structural decomposition), corrected** (Feng, Niazadeh & Saberi,
arXiv:2210.11648v1, pp.13–14, restated p.ec4; proof pp.ec5–ec6). Let `g` be differentiable,
monotone and strictly convex, let all weights be positive and let `x*` be an optimal solution of
`𝒫^g`. With `y*_j = Σ_i x*_{ij}`, `S⁽⁰⁾`, `D⁽⁰⁾`, the components of `G′[D₁ \ D⁽⁰⁾, S \ S⁽⁰⁾]` and the
level slacks `c⁽ˡ⁾` of `Def_TwoStageMatch_Decomposition`:
1. (uniformity) every supply `j` satisfies `w_j (1 − y*_j) = c⁽ˡ⁾` for its level `l`, and `c⁽⁰⁾ = 0`;
2. (monotonicity) for every edge `(i, j) ∈ E` with `i ∈ D₁` of level `l` and `j` of level `l′`,
   `c⁽ˡ′⁾ ≤ c⁽ˡ⁾` (no edge of `E` from `D⁽ˡ⁾` to `S⁽ˡ′⁾` when `c⁽ˡ⁾ < c⁽ˡ′⁾`);
3. (saturation) every `i ∈ D₁` lying in a component that contains a supply vertex is fully
   matched, `Σ_j x*_{ij} = 1`;
4. (supply-free components) a component that contains no supply vertex consists of a single
   demand vertex `i`, and every supply `j` with `(i, j) ∈ E` lies in `S⁽⁰⁾`.

The printed lemma claims saturation for every component `l ≥ 1`; that fails for a component
without supply vertices (see the item's natural-language statement), hence clauses 3 and 4. -/
theorem lemma_1 {D₁ D₂ S : Type*} [Fintype D₁] [Fintype S] [DecidableEq D₁] [DecidableEq S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (hw : ∀ j, 0 < I.w j)
    (x : D₁ → S → ℝ) (hx : IsOptimal I g x) :
    ((∀ j, I.w j * (1 - load x j) = levelSlack I.w x (levelS x j)) ∧
      levelSlack I.w x none = 0) ∧
    (∀ i j, I.E (Sum.inl i) j →
      levelSlack I.w x (levelS x j) ≤ levelSlack I.w x (levelD x i)) ∧
    (∀ i, levelD x i ≠ none → (∃ j, levelS x j = levelD x i) → ∑ j, x i j = 1) ∧
    (∀ i, levelD x i ≠ none → (¬ ∃ j, levelS x j = levelD x i) →
      (∀ i', levelD x i' = levelD x i → i' = i) ∧
      ∀ j, I.E (Sum.inl i) j → levelS x j = none) := by sorry

end TwoStageMatch
