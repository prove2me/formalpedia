-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_3_16
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_3_16
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:01:15.569469+00:00
-- url     : https://prove2.me/theorems/34f6341f-292d-423c-b92f-0d1163992456
-- title:
--   Lemma 3.16: Peirce reflection implies Cayley type
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $\tau$ be an involutive Lie automorphism reversing $W_{\min}$, and $\theta$ a commuting Cartan involution. Let $0
--   e h\in\mathfrak g$ satisfy $\tau h=h$, $\theta h=-h$, and $\mathfrak g=\mathfrak g_{-1}(h)\oplus\mathfrak g_0(h)\oplus\mathfrak g_1(h)$. Put $V=\mathfrak g_1(h)$ and give it the product $a\cdot b=\frac12[[a,y],b]$, unit $x$, and scalar product $-B(a,\theta b)$ from the compatible triple $(2h,x,y)$, as in Example 2.23. Let $\sigma=-\tau|_V$. A Peirce reflection means that $\sigma=P(2c-e)$ for an idempotent $c$, with $P(w)=2L(w)^2-L(w^2)$. Then
--
--   $$\sigma\text{ is a Peirce reflection}\quad\Longrightarrow\quad\tau\text{ is of Cayley type}.$$
--
--   Cayley type means that the symmetric pair $(\mathfrak g,\tau)$ is isomorphic to its real symmetric dual $\mathfrak g^\tau\oplus i\mathfrak g^{-\tau}$. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 25, Lemma 3.16

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

/-- Lemma 3.16, PDF p. 25. Peirce reflection is P(2c-e), as defined on p. 15. -/
theorem lemma_3_16 (hg : HermitianSimple (G := G)) (hb : RestrictedTubeType (G := G))
    (Wmin : Set G) (hm : MinimalCone Wmin) (tau theta : G ≃ₗ⁅ℝ⁆ G)
    (hp : CompatiblePair Wmin tau theta) (h : G) (hn : h ≠ 0)
    (hf : tau h = h) (ht : theta h = -h) (hd : ThreeGrading h)
    (J : EuclideanJordan (adSpace h 1)) (hj : KKTModel theta h 1 J)
    (a : JordanAuto J) (ha : ∀ v : adSpace h 1, (a.linear v : G) = -tau (v : G))
    (hr : PeirceReflection J a) : CayleyType tau := by sorry

end AdditionalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
