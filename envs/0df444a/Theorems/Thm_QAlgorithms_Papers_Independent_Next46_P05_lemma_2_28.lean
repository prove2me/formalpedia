-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_2_28
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_2_28
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:47:54.263108+00:00
-- url     : https://prove2.me/theorems/ab6da299-04f3-4e2a-a3bd-c3447824ba00
-- title:
--   Lemma 2.28: closed invariant-cone slices
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Assume $\mathfrak g$ is of tube type. Fix a Cartan involution $\theta$ and a hyperbolic $h\in\mathfrak p$ whose adjoint spectrum is exactly $\{-2,0,2\}$. Put $V=\mathfrak g_2(h)$ and give it the Jordan product and unit constructed from a compatible $\mathfrak{sl}_2$ triple in Example 2.23. Define $W_{\max}=\{a:B(a,w)\le0\text{ for all }w\in W_{\min}\}$ and $\Omega_V=\operatorname{int}\{v^2:v\in V\}$. Then
--
--   $$W_{\min}\cap V=W_{\max}\cap V\in\{\overline{\Omega_V},-\overline{\Omega_V}\}.$$
--
--   The closures are taken in $V$, and the same sign serves both intersections. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 13, Lemma 2.28

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

/-- Lemma 2.28, PDF p. 13. The original PDF has closure(Omega_V).
Comparison is in V=g_2(h), and one sign is shared by both invariant cones. -/
theorem lemma_2_28 (hg : HermitianSimple (G := G)) (hb : RestrictedTubeType (G := G))
    (theta : G ≃ₗ⁅ℝ⁆ G) (ht : Cartan theta) (h : G) (hp : theta h = -h)
    (hh : Hyperbolic h) (hsp : complexSpectrum (LieAlgebra.ad ℝ G h) = {-2, 0, 2})
    (J : EuclideanJordan (adSpace h 2)) (hj : KKTModel theta h 2 J)
    (Wmin : Set G) (hm : MinimalCone Wmin) :
    let M := (Subtype.val : adSpace h 2 → G) ⁻¹' Wmin
    let N := (Subtype.val : adSpace h 2 → G) ⁻¹' maximalCone Wmin
    M = N ∧ (M = closure (jordanOmega J) ∨ M = Neg.neg '' closure (jordanOmega J)) := by sorry

end AdditionalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
