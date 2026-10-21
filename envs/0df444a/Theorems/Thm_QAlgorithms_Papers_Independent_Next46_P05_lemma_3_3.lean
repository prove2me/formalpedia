-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_3_3
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_3_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:53:15.961981+00:00
-- url     : https://prove2.me/theorems/023c3d5d-5338-445e-986f-0521b80ea5e8
-- title:
--   Lemma 3.3: ambient inner conjugacy of fixed hyperbolic elements
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Assume $\mathfrak g$ is semisimple. Let $\theta$ be a Cartan involution and $\tau$ an involutive Lie automorphism commuting with it. Put $\mathfrak p=\mathfrak g^{-\theta}$. Let $\mathfrak a\subseteq\mathfrak p$ be maximal abelian and assume $\mathfrak a\cap\mathfrak g^\tau$ is maximal abelian in $\mathfrak g^\tau\cap\mathfrak p$. For every $h\in\mathfrak g^\tau$ hyperbolic in the ambient algebra,
--
--   $$\exists\phi\in\operatorname{Inn}(\mathfrak g^\tau):\quad \phi(h)\in\mathfrak a\cap\mathfrak g^\tau.$$
--
--   The inner group acts on $\mathfrak g$ by finite products of $\exp(\operatorname{ad}x)$ with $x\in\mathfrak g^\tau$. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 18, Lemma 3.3

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

/-- Lemma 3.3, PDF p. 18. Conjugation is the ambient action of Inn(g^tau). -/
theorem lemma_3_3 [LieAlgebra.IsSemisimple ℝ G] (theta tau : G ≃ₗ⁅ℝ⁆ G)
    (ht : Cartan theta) (hu : Function.Involutive tau)
    (hc : ∀ x, theta (tau x) = tau (theta x)) (A : Submodule ℝ G)
    (hA : MaximalAbelianIn A (autoSpace theta (-1)))
    (hAh : MaximalAbelianIn (A ⊓ autoSpace tau 1)
      (autoSpace tau 1 ⊓ autoSpace theta (-1)))
    (h : G) (hh : tau h = h) (hb : Hyperbolic h) :
    ∃ phi : G ≃ₗ⁅ℝ⁆ G, InnerFixed tau phi ∧ phi h ∈ A ⊓ autoSpace tau 1 := by sorry

end LieStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
