-- Prove2me | Theorems.Thm_PConeEB_proposition_2_1
-- name    : PConeEB.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:03.065581+00:00
-- url     : https://prove2.me/theorems/bac70491-7883-4d60-a718-c7b2b51d2ee5
-- title:
--   Proposition 2.1 — error bound under the PPS condition
-- statement:
--   Let $K$ be a closed convex cone in a finite dimensional Euclidean space, $\mathcal L$ a subspace and $a$ a point with $(\mathcal L+a)\cap K\ne\emptyset$. If (Feas) satisfies the partial-polyhedral Slater condition, then $K$ and $\mathcal L+a$ satisfy a Lipschitzian error bound.
--
--   This is the base case of the facial reduction strategy: an error bound holds outright as soon as a constraint qualification holds. The paper cites it from Bauschke, Borwein and Li (1999), Corollary 3.
--
--   Differences from the source:
--   - reading: the feasibility of (Feas) is not printed in the statement → (L + a) ∩ K nonempty is a hypothesis; reason: Definition 2.1 is stated only for sets that meet, and PPS (i) does not supply it, so the printed conclusion is undefined without it
--   - generalization: K = K¹ × K² in PPS (iii) → K = K₁ + K₂ with K₁ ⊆ E₁, K₂ ⊆ E₂ for complementary subspaces E₁, E₂, not necessarily orthogonal; reason: orthogonal subspaces are the Cartesian case, so the hypothesis is weaker and the result covers the source; a linear isomorphism preserves polyhedrality, ri and Lipschitzian error bounds up to constants
--   - encoding: a finite dimensional Euclidean space E → a type E with InnerProductSpace ℝ E and FiniteDimensional ℝ E; reason: Mathlib conventions; the same instances
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Proposition 2.1, p.3

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_PConeEB_IsPPS
import Definitions.Def_PConeEB_IsUniformHolderianEB

open MoreauProx.Decomposition (IsClosedConvexCone)

namespace PConeEB

/-- Proposition 2.1 (error bound under the PPS condition): if (Feas) satisfies the PPS condition,
then a Lipschitzian error bound holds between `K` and `L + a`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Proposition 2.1, p.3 (from Bauschke, Borwein & Li,
1999, Corollary 3).

**Formalization Note.** Feasibility `(L + a) ∩ K ≠ ∅` is implicit in the page: Definition 2.1 is
stated only for sets that meet, and PPS alternative (i) does not supply it. -/
theorem proposition_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosedConvexCone K)
    (L : Submodule ℝ E) (a : E) (hfeas : (affineSet L a ∩ K).Nonempty)
    (hPPS : IsPPS K L a) :
    IsUniformHolderianEB K (affineSet L a) 1 := by sorry

end PConeEB
