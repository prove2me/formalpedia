-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_corollary_3_10
-- name    : QAlgorithms.Papers.Independent.Next46.P05.corollary_3_10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:58:15.032737+00:00
-- url     : https://prove2.me/theorems/3c68baed-3445-4f4a-8557-defe91e1e216
-- title:
--   Corollary 3.10: embedded equality with a bounded-spectrum hyperbolic representative
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $W$ be any pointed generating invariant closed convex cone, and let $\tau$ be an involutive Lie automorphism with $\tau W=-W$. For every $h\in\mathfrak g^\tau$, there exists $h_0\in\mathfrak g^\tau$ such that
--
--   $$h_0\text{ is hyperbolic},\qquad \operatorname{spec}(\operatorname{ad}h_0)\subseteq\{0,\pm\tfrac12,\pm1\},\qquad
--   \mathfrak g(\tau,h)=\mathfrak g(\tau,h_0).$$
--
--   Both causal algebras use $W_{\min}$ and are equal as embedded subalgebras. The original $h$ need not be hyperbolic. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 23, Corollary 3.10

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

/-- Corollary 3.10, PDF p. 23. Original h is arbitrary; equality is embedded equality.
The preamble's W is retained while g(tau,h) uses the chosen Wmin. -/
theorem corollary_3_10 (hg : HermitianSimple (G := G)) (Wmin W : Set G)
    (hm : MinimalCone Wmin) (hw : GeneratingInvariantCone W)
    (tau : G ≃ₗ⁅ℝ⁆ G) (ht : Function.Involutive tau)
    (hr : tau '' W = Neg.neg '' W) (h : G) (hh : tau h = h) :
    ∃ h0 : G, tau h0 = h0 ∧ Hyperbolic h0 ∧
      complexSpectrum (LieAlgebra.ad ℝ G h0) ⊆ fiveSpectrum ∧
      causalAlgebra Wmin tau h = causalAlgebra Wmin tau h0 := by sorry

end LieStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
