-- Prove2me | Theorems.Thm_WeldedPath_single_cycle_completion_count
-- name    : WeldedPath.single_cycle_completion_count
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T18:28:11.449975+00:00
-- url     : https://prove2.me/theorems/547dd670-c0ce-41d5-948b-7caba6165da7
-- title:
--   Conditional partner counts for single-cycle weld completions
-- statement:
--   Let $G$ be a valid properly three-colored welded-tree instance, with $n$ even and $2\le l\le n-4$. Let $S$ be the finite set of edge permutations preserving the allowed edge classes whose permuted weld is a single cycle. Fix any set $D$ of exposed input edges and any reference permutation $h$. Put
--   $$
--   F=\{\pi\in S:\ \pi(d)=h(d)\text{ for all }d\in D\}.
--   $$
--   For a weld edge $e\notin D$, let $C(e)$ be the weld edges of the same color as $e$, and put $r=|C(e)\setminus D|$. Then, for every target edge $z$,
--   $$
--   (r-1)\,|\{\pi\in F:\pi(e)=z\}|\le |F|.
--   $$
--
--   For $F\ne\varnothing$ and $r\ge2$, this is precisely the conditional partner bound $\Pr[\pi(e)=z\mid\pi\in F]\le1/(r-1)$. The formal statement uses natural-number counts and truncated subtraction, so empty conditioning fibers and singleton residual classes require no separate hypotheses. A recorded or wrong-class target has zero count by injectivity or class preservation. Conditioning on nonweld records is allowed: those independent class-permutation coordinates do not affect the cycle condition.
--
--   The statement is solely a finite completion count. It asserts no coupling, random process, quantum claim, or path distribution. Counting is over colored edge permutations, not over their uncolored graph images.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1#S4.SS4, Section 4.4, proof of Lemma 4.13, equation (76) and its path-deletion/insertion and endpoint-symmetry argument. The probability inequality is multiplied by the positive completion count and residual denominator; empty and singleton cases are included trivially. Arbitrary records outside the tested color are handled by conditioning on complete assignments of the other colors and averaging, with independent nonweld coordinates factored out.

import Definitions.Def_WeldedPath_successProb
import Definitions.Def_FinitePermutationCoupling_BlockModel

set_option autoImplicit false

namespace WeldedPath

open Classical FinitePermutationCoupling

/-- The static conditional completion count underlying equation (76) in the
proof of Lemma 4.13, arXiv:2611.05912v1, Section 4.4. The factor uses truncated
natural subtraction, so empty fibers and one remaining partner are included.
No stochastic process, coupling, or path law is asserted here. -/
theorem single_cycle_completion_count :
    ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedInstance n, G.IsValid →
    ∀ (D : Finset G.edges) (h : Equiv.Perm G.edges) (e z : G.edges),
      e.1 ∈ G.weldEdges → e ∉ D →
      (((Finset.univ.filter fun f : G.edges =>
          f.1 ∈ G.weldEdges ∧ G.color f.1 = G.color e.1) \ D).card - 1) *
        ((exposedFiber
          ((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle) D h).filter
            fun π => π e = z).card ≤
        (exposedFiber
          ((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle) D h).card := by
  sorry

end WeldedPath
