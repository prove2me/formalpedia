-- Prove2me | Theorems.Thm_WeldedPath_single_cycle_coupling
-- name    : WeldedPath.single_cycle_coupling
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T17:34:22.686535+00:00
-- url     : https://prove2.me/theorems/eb15a0a6-8125-4952-a18a-211aa9967b7f
-- title:
--   Coupling single-cycle and product welded-tree distributions
-- statement:
--   There is an absolute constant $K>0$ with the following property. Let $n$ be even, $2\le l\le n-4$, and let $G$ be a valid properly three-colored welded-tree instance whose single-cycle support $S$ is nonempty. Put $P=\operatorname{prodSupport}(G,l)$. There is a nonnegative joint weight $w(h,g)$ on pairs of label-and-edge permutations with uniform marginals on $S$ and $P$. For every fixed first sample $h$ and every query input $x$,
--   $$
--   \sum_g w(h,g)\,\mathbf1[O_g(x)\ne O_h(x)] \le \frac{Kn}{2^n}\,\frac{\mathbf1[h\in S]}{|S|}.
--   $$
--
--   All sums range over the full finite permutation space. Zero marginal mass and nonnegativity force zero joint mass outside $S\times P$. The disagreement bound is conditional on each entire single-cycle sample, rather than merely averaged over that distribution. The statement concerns only the graph distributions and their classical oracle answers; it has no algorithm, workspace, or query-count parameter. It is the coupling input to the quantum hybrid argument.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1#S4.SS4. Section 4.4, proof of Lemma 4.13: conditional matching-partner estimate (76), random-order swap coupling, (77), and the conditional oracle-disagreement display immediately after (77), before the quantum hybrid argument. The joint law is expressed as finite real weights with explicit uniform marginals; the first coordinate is the single-cycle sample. The target hypotheses imply n>=6. Any finite exceptions below the source section's n>=16 convention are covered by independent coupling after increasing the absolute constant.

import Definitions.Def_WeldedPath_successProb

namespace WeldedPath

open QAlgorithms
open scoped BigOperators

/-- The finite coupling constructed in the proof of Lemma 4.13, before the quantum
hybrid argument (Carolan et al., arXiv:2611.05912v1, Section 4.4, equations (76)--(77)
and the conditional oracle-disagreement display following (77)).

The first marginal is uniform on `singSupport`; the second is uniform on
`prodSupport`. For EACH fixed single-cycle sample and EACH query input, the
conditional probability of different oracle answers is at most `K*n/2^n`.
The joint weights are extended by zero off the product of the two supports.
There are no quantum-algorithm parameters in this combinatorial statement. -/
theorem single_cycle_coupling :
    ∃ K : ℝ, 0 < K ∧
      ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid → (G.singSupport l).Nonempty →
      ∃ w : (Equiv.Perm (Label n) × Equiv.Perm G.edges) →
          (Equiv.Perm (Label n) × Equiv.Perm G.edges) → ℝ,
        (∀ σh σg, 0 ≤ w σh σg) ∧
        (∀ σh, (∑ σg, w σh σg) =
          if σh ∈ G.singSupport l then 1 / ((G.singSupport l).card : ℝ) else 0) ∧
        (∀ σg, (∑ σh, w σh σg) =
          if σg ∈ G.prodSupport l then 1 / ((G.prodSupport l).card : ℝ) else 0) ∧
        (∀ σh (x : Qubits (2 * n + 1) × Fin 3),
          (∑ σg, if G.oracleFn l σg x ≠ G.oracleFn l σh x then w σh σg else 0) ≤
            (K * (n : ℝ) / (2 : ℝ) ^ n) *
              (if σh ∈ G.singSupport l then 1 / ((G.singSupport l).card : ℝ) else 0)) := by
  sorry

end WeldedPath
