-- Prove2me | Theorems.Thm_WeldedPath_single_cycle_switching_chain
-- name    : WeldedPath.single_cycle_switching_chain
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T17:55:33.007144+00:00
-- url     : https://prove2.me/theorems/1048e049-f74a-4d75-bdc3-268735eeed60
-- title:
--   Random-order switching chain for single-cycle colored matchings
-- statement:
--   Let $N=2^n$, with $n$ even and $2\le l\le n-4$, and let $G$ be a valid properly three-colored welded-tree instance with nonempty single-cycle support. Let $P$ be the finite set of class-preserving edge permutations, and let $S$ be its single-cycle subset. There is a nonnegative joint weight $v(h,p)$ on reference edge permutations $h$ and paths $p:\{0,\ldots,N\}\to\operatorname{Perm}(E)$. Its reference marginal is uniform on $S$; every positive-weight path has $p(N)=h$; and the marginal of $p(0)$ is uniform on $P$. For each fixed reference $h$, each original edge $e$, and each $0\le i<N$,
--   $$\sum_p v(h,p)\mathbf1[p(i)(e)\ne p(i+1)(e)] \le \frac{4}{N(i+1)}\frac{\mathbf1[h\in S]}{|S|}.$$
--
--   The path index is the remaining matching size, so the random-order process runs from $N$ down to zero. A color class of size $m$ is padded with identity stages above $m$; its final deterministic stage may also be an identity. All distributions retain the original colored edge-permutation coordinates. The statement is the stochastic construction only: it asserts no bound on oracle answers and contains no quantum algorithm, label permutation, or query-count parameter. Endpoint disagreement and the harmonic estimate are proved separately from this certificate.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1#S4.SS4, Section 4.4, proof of Lemma 4.13. Equation (76) bounds a conditional matching partner by 1/(r-1). The following random-order residual-matrix swap process has the exact product-uniform output law. At remaining size r, a fixed forward matching entry is affected with probability at most 2/(m*r), conditional on the entire reference sample. Proper three-coloring gives N/2<=m<=N for each weld-color class, yielding the displayed 4/(N*r) certificate. Stages may be recorded jointly across the disjoint color classes because a fixed edge belongs to one class. Nonweld classes are copied. No quotient by the uncolored simple graph is taken, avoiding changes to the original sampling multiplicities. This child remains an open finite stochastic-construction obligation; the formal endpoint union bound, inverse-image transfer, harmonic bound, label lifting, and oracle lifting are supplied by the parent proof.

import Definitions.Def_WeldedPath_successProb

namespace WeldedPath

open Classical
open scoped BigOperators

/-- The random-order switching construction underlying Lemma 4.13 of Carolan et al.,
arXiv:2611.05912v1, Section 4.4, equation (76) and the subsequent coupling process.

The path is indexed backwards by the number of remaining entries: its last state is
the reference single-cycle edge permutation and its zeroth state has the product
law. An adjacent transition indexed by `i` corresponds to remaining count `i+1`.
Each color class uses its original colored matching coordinates; unused stages are
identity transitions. The statement concerns only forward images of fixed edges.
It contains neither labels nor quantum algorithms nor an oracle-disagreement bound. -/
theorem single_cycle_switching_chain :
    ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedInstance n, G.IsValid → (G.singSupport l).Nonempty →
    ∃ v : Equiv.Perm G.edges →
        (Fin (2 ^ n + 1) → Equiv.Perm G.edges) → ℝ,
      (∀ h p, 0 ≤ v h p) ∧
      (∀ h, (∑ p, v h p) =
        if h ∈ ((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle) then
          1 / (((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle).card : ℝ)
        else 0) ∧
      (∀ h p, v h p ≠ 0 → p (Fin.last (2 ^ n)) = h) ∧
      (∀ g, (∑ h, ∑ p, if p 0 = g then v h p else 0) =
        if g ∈ Finset.univ.filter (G.IsEdgePerm l) then
          1 / ((Finset.univ.filter (G.IsEdgePerm l)).card : ℝ) else 0) ∧
      (∀ h (e : G.edges) (i : Fin (2 ^ n)),
        (∑ p, if (p i.castSucc) e ≠ (p i.succ) e then v h p else 0) ≤
          (4 / ((2 : ℝ) ^ n * ((i.val : ℝ) + 1))) *
            (if h ∈ ((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle) then
              1 / (((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle).card : ℝ)
            else 0)) := by
  sorry

end WeldedPath
