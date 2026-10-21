-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_theorem_3_14
-- name    : QAlgorithms.Papers.Independent.Next46.P05.theorem_3_14
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:00:00.363772+00:00
-- url     : https://prove2.me/theorems/8d58a19e-92bf-4247-9470-c28d8e56f0c3
-- title:
--   Theorem 3.14: full simultaneous eigenspaces and the tube-type dichotomy
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $\tau$ be an involutive Lie automorphism reversing $W_{\min}$, and $\theta$ a commuting Cartan involution. Let $0
--   e h\in\mathfrak g$ satisfy $\tau h=h$, $\theta h=-h$, and $\mathfrak g=\mathfrak g_{-1}(h)\oplus\mathfrak g_0(h)\oplus\mathfrak g_1(h)$. Then
--
--   $$\mathfrak g(\tau,h)=\mathfrak g^{-\tau}_{-1}(h)\oplus[\mathfrak g^{-\tau}_{-1}(h),\mathfrak g^{-\tau}_1(h)]\oplus\mathfrak g^{-\tau}_1(h).$$
--
--   Here $\mathfrak g^{-\tau}_t(h)=\{x:\tau x=-x,[h,x]=tx\}$, and the sum is internally independent. Moreover, this causal algebra is either hermitian simple of tube type or an internal direct sum of two hermitian simple tube-type ideals. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 24, Theorem 3.14

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

section LieStatements

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Theorem 3.14, PDF p. 24. Both full simultaneous eigenspace equality and the
one/two simple tube-type alternatives are conclusions. -/
theorem theorem_3_14 (hg : HermitianSimple (G := G)) (hb : RestrictedTubeType (G := G))
    (Wmin : Set G) (hm : MinimalCone Wmin) (tau theta : G ≃ₗ⁅ℝ⁆ G)
    (hp : CompatiblePair Wmin tau theta) (h : G) (hn : h ≠ 0)
    (hf : tau h = h) (ht : theta h = -h) (hd : ThreeGrading h) :
    DirectThree (causalAlgebra Wmin tau h).toSubmodule
      (adSpace h (-1) ⊓ autoSpace tau (-1))
      (bracketSpan (adSpace h (-1) ⊓ autoSpace tau (-1)) (adSpace h 1 ⊓ autoSpace tau (-1)))
      (adSpace h 1 ⊓ autoSpace tau (-1)) ∧
    ((HermitianSimple (G := causalAlgebra Wmin tau h) ∧
      RestrictedTubeType (G := causalAlgebra Wmin tau h)) ∨
    ∃ I J : LieIdeal ℝ (causalAlgebra Wmin tau h),
      IsCompl I.toSubmodule J.toSubmodule ∧
      HermitianSimple (G := I) ∧ RestrictedTubeType (G := I) ∧
      HermitianSimple (G := J) ∧ RestrictedTubeType (G := J)) := by sorry

end LieStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
