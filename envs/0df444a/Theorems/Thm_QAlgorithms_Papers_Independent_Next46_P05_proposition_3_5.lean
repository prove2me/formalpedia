-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_proposition_3_5
-- name    : QAlgorithms.Papers.Independent.Next46.P05.proposition_3_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:54:54.315337+00:00
-- url     : https://prove2.me/theorems/4f434606-af21-4175-b41a-1d9ef87f4c97
-- title:
--   Proposition 3.5: the specified coefficient cutoff preserves both cones
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $\tau$ be an involutive Lie automorphism reversing $W_{\min}$, and $\theta$ a commuting Cartan involution. Assume tube type and use the Section 3.1 normalized coroot basis $H_1,\ldots,H_r$ of a maximal abelian $\mathfrak a\subset\mathfrak p$, with $H=\frac12\sum_kH_k$ and $\tau=\exp(i\pi\operatorname{ad}H)$. Let $h=\sum_k\lambda_kH_k$ and suppose $\mathfrak g_1(h)\subseteq\mathfrak g_1(H)$. Define $h\prime=\sum_k\lambda_k\prime H_k$ with $\lambda_k\prime=1/2$ when $\lambda_k=1/2$, and $0$ otherwise. Then, for $C_\pm(a)=(\pm W_{\min})\cap\mathfrak g^{-\tau}_{\pm1}(a)$,
--
--   $$C_-(h)=C_-(h\prime),\qquad C_+(h)=C_+(h\prime).$$
--
--   The new element is the specified coefficient cutoff, not an arbitrary witness. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 19, Proposition 3.5

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

/-- Proposition 3.5, PDF p. 19. h' is computed by the source's piecewise coefficients. -/
theorem proposition_3_5 (hg : HermitianSimple (G := G)) (hb : RestrictedTubeType (G := G))
    (Wmin : Set G) (hm : MinimalCone Wmin) (tau theta : G ≃ₗ⁅ℝ⁆ G)
    (hp : CompatiblePair Wmin tau theta) (B : CayleyCoordinates Wmin tau theta)
    (lam : Fin B.rank → ℝ)
    (hi : adSpace (coefficientElement B lam) 1 ≤ adSpace (coordinateH B) 1) :
    causalSlice Wmin tau (coefficientElement B lam) (-1) =
      causalSlice Wmin tau (cutElement B lam) (-1) ∧
    causalSlice Wmin tau (coefficientElement B lam) 1 =
      causalSlice Wmin tau (cutElement B lam) 1 := by sorry

end AdditionalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
