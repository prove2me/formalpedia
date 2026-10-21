-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_3_6
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_3_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:55:30.42031+00:00
-- url     : https://prove2.me/theorems/6715ba0a-7510-4613-a3e6-cf61450a2cb1
-- title:
--   Lemma 3.6: positive cones are simple partial-unit corners
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $\tau$ be an involutive Lie automorphism reversing $W_{\min}$, and $\theta$ a commuting Cartan involution. Use the tube-type coroot/Jordan-frame data of Section 3.1: $H=\frac12\sum_{i=1}^rH_i$, $V=\mathfrak g_1(H)$, its constructed euclidean Jordan algebra, frame $(X_i)$ normalized by $L(X_i)=\frac12\operatorname{ad}H_i|_V$, and orientation $C=W_{\min}\cap V=\{x^2:x\in V\}$. For $1\le s\le r$, set $h=\frac12\sum_{i=1}^sH_i$ and $V^{(s)}=V_1(X_1+\cdots+X_s)$. Then
--
--   $$C_+(h)=C\cap V^{(s)},\qquad \operatorname{span}_{\mathbb R}C_+(h)=V^{(s)},\qquad V^{(s)}\text{ is simple}.$$
--
--   The corner has its induced Jordan product and partial unit. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 20, Lemma 3.6

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

/-- Lemma 3.6, PDF p. 20. Square cones, induced product, and the partial-unit corner. -/
theorem lemma_3_6 (hg : HermitianSimple (G := G)) (hb : RestrictedTubeType (G := G))
    (Wmin : Set G) (hm : MinimalCone Wmin) (tau theta : G ≃ₗ⁅ℝ⁆ G)
    (hp : CompatiblePair Wmin tau theta) (B : CayleyCoordinates Wmin tau theta)
    (F : CayleyJordanFrame B) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ B.rank) :
    let h := coefficientElement B (fun i => if i.val < s then (1 / 2 : ℝ) else 0)
    let V := peirce F.J (partialUnit F.c s) 1
    causalSlice Wmin tau h 1 =
      (Subtype.val : adSpace (coordinateH B) 1 → G) '' (squares F.J ∩ (V : Set _)) ∧
    Submodule.span ℝ (causalSlice Wmin tau h 1) =
      V.map (adSpace (coordinateH B) 1).subtype ∧ SimpleJordanIn F.J V := by sorry

end AdditionalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
