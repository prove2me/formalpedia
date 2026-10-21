-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_2_41
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_2_41
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:51:36.146988+00:00
-- url     : https://prove2.me/theorems/8200053a-e169-4830-8be1-e5da7875bec8
-- title:
--   Lemma 2.41: the constructed paired Jordan frame
-- statement:
--   Let $V$ be a finite-dimensional real unital euclidean Jordan algebra, with bilinear Jordan product, unit $e$, and a positive definite associative scalar product. Assume $V$ is simple. Let $\alpha$ be a non-split involutive Jordan automorphism and let $F=(c_1,\ldots,c_{2s})$ be a Jordan frame with $\alpha(F)=F$ and $\alpha(\{c_1,\ldots,c_s\})\cap\{c_1,\ldots,c_s\}=\varnothing$. Then
--
--   $$F_+=\{c_k+\alpha(c_k):1\le k\le s\}\text{ is a Jordan frame of }V^\alpha.$$
--
--   The frame is constructed from exactly $s$ pair-sums, with its product and unit inherited from $V$. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 17, Lemma 2.41

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

section JordanStatements

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Lemma 2.41, PDF p. 17. The resulting frame is the specified s pair-sums. -/
theorem lemma_2_41 (J : EuclideanJordan V) (hs : SimpleJordanIn J ⊤)
    (a : JordanAuto J) (ha : Function.Involutive a.linear) (hn : NonSplit J a)
    {s : ℕ} (c : Fin (2 * s) → V) (hf : JordanFrame J c)
    (hstable : a.linear '' Set.range c = Set.range c)
    (hdisjoint : Disjoint
      (a.linear '' {x | ∃ i : Fin (2 * s), i.val < s ∧ x = c i})
      {x | ∃ i : Fin (2 * s), i.val < s ∧ x = c i}) :
    FrameIn J (jordanFixed J a) J.unit (pairedFrame c a.linear) := by sorry

end JordanStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
