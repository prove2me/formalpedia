-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_theorem_3_17
-- name    : QAlgorithms.Papers.Independent.Next46.P05.theorem_3_17
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:02:10.418996+00:00
-- url     : https://prove2.me/theorems/5fdc0655-19df-40ba-b3cd-9f96164260b2
-- title:
--   Theorem 3.17: all three rank and involution-type conclusions
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $\tau$ be an involutive Lie automorphism reversing $W_{\min}$, and $\theta$ a commuting Cartan involution. Let $0
--   e h\in\mathfrak g$ satisfy $\tau h=h$, $\theta h=-h$, and $\mathfrak g=\mathfrak g_{-1}(h)\oplus\mathfrak g_0(h)\oplus\mathfrak g_1(h)$. Put $V=\mathfrak g_1(h)$ and give it the product $a\cdot b=\frac12[[a,y],b]$, unit $x$, and scalar product $-B(a,\theta b)$ from the compatible triple $(2h,x,y)$, as in Example 2.23. Let $\sigma=-\tau|_V$, and distinguish real Lie rank from Jordan frame rank. Then
--
--   1. If $\tau$ is Cayley type, $\sigma$ is a Peirce reflection.
--   2. If $\tau$ is not Cayley type and $\operatorname{rank}_{\mathbb R}\mathfrak g^\tau=\operatorname{rank}_{\mathbb R}\mathfrak g$, then $V^\sigma$ is simple and nonzero, and $\operatorname{rank}V^\sigma=\operatorname{rank}V$.
--   3. If $\operatorname{rank}_{\mathbb R}\mathfrak g=2\operatorname{rank}_{\mathbb R}\mathfrak g^\tau$, then
--
--   $$2\operatorname{rank}V^\sigma=\operatorname{rank}V.$$
--
--   No orthogonal-family exclusion is imposed on this theorem. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 25, Theorem 3.17

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P05

namespace QAlgorithms.Papers.Independent.Next46.P05

noncomputable section

open Set

open QAlgorithms.Papers.Independent.Frontier30.P26
  (bracketSpan innerWord Invariant ClosedCone GeneratingInvariantCone CompactlyEmbedded)

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P05.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P05.lieNormedSpace

section AdditionalStatements

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Theorem 3.17(a)–(c), PDF pp. 25–26. Lie split rank and Jordan frame rank are distinct.
The theorem does not exclude so(2,n). -/
theorem theorem_3_17 (hg : HermitianSimple (G := G)) (hb : RestrictedTubeType (G := G))
    (Wmin : Set G) (hm : MinimalCone Wmin) (tau theta : G ≃ₗ⁅ℝ⁆ G)
    (hp : CompatiblePair Wmin tau theta) (h : G) (hn : h ≠ 0)
    (hf : tau h = h) (ht : theta h = -h) (hd : ThreeGrading h)
    (J : EuclideanJordan (adSpace h 1)) (hj : KKTModel theta h 1 J)
    (a : JordanAuto J) (ha : ∀ v : adSpace h 1, (a.linear v : G) = -tau (v : G)) :
    (CayleyType tau → PeirceReflection J a) ∧
    ((¬ CayleyType tau ∧ realRank (G := fixedLie tau) = realRank (G := G)) →
      SimpleJordanIn J (jordanFixed J a) ∧ JordanSplit J a) ∧
    (realRank (G := G) = 2 * realRank (G := fixedLie tau) → NonSplit J a) := by sorry

end AdditionalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
