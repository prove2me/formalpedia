-- Prove2me | Theorems.Thm_SteinerCutDominants_remark_1
-- name    : SteinerCutDominants.remark_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:58.737991+00:00
-- url     : https://prove2.me/theorems/c2a9b1d4-612b-4888-911d-e97f3b13767a
-- title:
--   Remark 1: when a valid inequality defines a facet of $\mathrm{CUT}_+(G,T)$
-- statement:
--   Let $(G,T)$ be a Steiner graph and $a\in\mathbb R^{E(G)}$ such that $ax\ge\gamma=\gamma_a(G,T)$ is valid for $\mathrm{CUT}_+(G,T)$.
--
--   1. If $\gamma=0$, the inequality defines a facet of $\mathrm{CUT}_+(G,T)$ if and only if it is a nonnegativity constraint.
--   2. If $\gamma>0$, the inequality defines a facet of $\mathrm{CUT}_+(G,T)$ if and only if $(G_a,T)$ has $|E_a|$ many $a$-minimum $T$-Steiner cuts that are linearly independent. For a family of such cuts, linear independence is equivalent to affine independence.
--
--   This reduces the facets of the dominant to linear algebra on minimum cuts of the support graph, and it is the link between polyhedra and facet inducing Steiner graphs.
--
--   Differences from the source:
--   - generalization: vector c in minimum integer form → any real vector a; reason: the claim does not depend on scaling or integrality; the page's c is the case a = c, and the goal theorem needs real a
--   - encoding: |E_c| many c-minimum cuts of (G_c, T) → a family of roots of a in G indexed by E_a, restricted to E_a; reason: for γ > 0 each root of G restricts to a minimum cut of G_a, and each minimum cut of G_a extends to a root of G
--   - encoding: nonnegativity constraint → a = r·e_f with r > 0; reason: a positive multiple of x_f ≥ 0
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Remark 1, p.4

import Mathlib
import Definitions.Def_SteinerCutDominants_DefinesFacet
import Definitions.Def_SteinerCutDominants_IsRootOf

open Matrix

namespace SteinerCutDominants

/-- **Remark 1** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.4). For each
inequality `a x ≥ γ = γ_a(G, T)` valid for `CUT₊(G, T)`: (1) if `γ = 0` it defines a facet iff it is
a nonnegativity constraint; (2) if `γ > 0` it defines a facet iff `(G_a, T)` has `|E_a|` many
`a`-minimum `T`-Steiner cuts that are linearly independent, which is equivalent to them being
affinely independent.

**Formalization Note** `a` is real, not yet scaled. A nonnegativity constraint is a positive multiple
of `x_e ≥ 0`. The cuts of `(G_a, T)` are the restrictions to `E_a` of the roots of `a` in `G`, and a
family of `|E_a|` of them is indexed by `E_a` itself. Connectivity of `G_a` is not assumed. -/
theorem remark_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hG : G.Connected) (hT : 2 ≤ T.card) (a : G.edgeSet → ℝ)
    (hvalid : ∀ y ∈ cutDominant G T, gammaOf G T a ≤ a ⬝ᵥ y) :
    (gammaOf G T a = 0 →
      (DefinesFacet G T a (gammaOf G T a) ↔ ∃ (e : G.edgeSet) (r : ℝ), 0 < r ∧ a = Pi.single e r)) ∧
    (0 < gammaOf G T a →
      (DefinesFacet G T a (gammaOf G T a) ↔
        ∃ S : {e : G.edgeSet // a e ≠ 0} → Finset V, (∀ e, IsRootOf G T a (S e)) ∧
          LinearIndependent ℝ
            (fun e : {e : G.edgeSet // a e ≠ 0} =>
              fun f : {e : G.edgeSet // a e ≠ 0} => cutVec G (S e) f.1)) ∧
      ∀ {ι : Type} (S : ι → Finset V), (∀ i, IsRootOf G T a (S i)) →
        (LinearIndependent ℝ
            (fun i : ι => fun f : {e : G.edgeSet // a e ≠ 0} => cutVec G (S i) f.1) ↔
          AffineIndependent ℝ
            (fun i : ι => fun f : {e : G.edgeSet // a e ≠ 0} => cutVec G (S i) f.1))) := by sorry

end SteinerCutDominants
