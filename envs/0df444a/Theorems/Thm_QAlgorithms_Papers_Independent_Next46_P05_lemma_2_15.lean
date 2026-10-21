-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_2_15
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_2_15
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:47:17.703024+00:00
-- url     : https://prove2.me/theorems/b4509ae4-9b90-4f51-b230-01ff74ce0883
-- title:
--   Lemma 2.15: H-element signs and cone reversal
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Fix a Cartan decomposition $\mathfrak g=\mathfrak k\oplus\mathfrak p$. Let $\tau$ be an involutive Lie automorphism preserving both summands. Let $H_0\in\mathfrak z(\mathfrak k)$ be an H-element, so its complexified adjoint is semisimple with exact spectrum $\{0,i,-i\}$. Let $W_{\min}(H_0)$ be the smallest pointed generating invariant closed convex cone containing $H_0$. Then
--
--   $$\tau H_0\in\{H_0,-H_0\},\qquad \tau W_{\min}(H_0)=-W_{\min}(H_0)\ \Longleftrightarrow\ \tau H_0=-H_0.$$
--
--   Both the sign dichotomy and its cone criterion are asserted. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 9, Lemma 2.15

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

/-- Lemma 2.15, PDF p. 9. Both the H-element sign dichotomy and the cone iff.
Commutation with theta expresses preservation of BOTH k and p. -/
theorem lemma_2_15 (hg : HermitianSimple (G := G)) (theta tau : G ≃ₗ⁅ℝ⁆ G)
    (ht : Cartan theta) (hu : Function.Involutive tau)
    (hc : ∀ x, theta (tau x) = tau (theta x)) (H0 : G) (hh : CartanHElement theta H0) :
    (tau H0 = H0 ∨ tau H0 = -H0) ∧
    (tau '' minimalConeAt H0 = Neg.neg '' minimalConeAt H0 ↔ tau H0 = -H0) := by sorry

end AdditionalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
