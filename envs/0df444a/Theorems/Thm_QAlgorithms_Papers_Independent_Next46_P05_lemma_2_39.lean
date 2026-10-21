-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_2_39
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_2_39
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:49:32.795983+00:00
-- url     : https://prove2.me/theorems/e769fb36-c339-4c6d-97de-d880b0c8b6e2
-- title:
--   Lemma 2.39: primitive fixed idempotent corner ranks
-- statement:
--   Let $V$ be a finite-dimensional real unital euclidean Jordan algebra, with bilinear Jordan product, unit $e$, and a positive definite associative scalar product. Assume $V$ is simple and $\alpha$ is an involutive Jordan automorphism. Let $c$ be a nonzero primitive idempotent of the fixed algebra $V^\alpha$, and put $W=V_1(c)=\{v:c\cdot v=v\}$ with its induced product and unit $c$. Then
--
--   $$\operatorname{rank}W=1\text{ if }\operatorname{rank}V^\alpha=\operatorname{rank}V,\qquad
--   \operatorname{rank}W=2\text{ if }2\operatorname{rank}V^\alpha=\operatorname{rank}V.$$
--
--   Jordan rank is the cardinality of an actual Jordan frame, not vector-space dimension. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 17, Lemma 2.39

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

/-- Lemma 2.39, PDF p. 17. The initial primitivity is in V^alpha. -/
theorem lemma_2_39 (J : EuclideanJordan V) (hs : SimpleJordanIn J ⊤)
    (a : JordanAuto J) (ha : Function.Involutive a.linear) (c : V)
    (hc : PrimitiveIn J (jordanFixed J a) c) :
    (JordanSplit J a → HasJordanRank J (peirce J c 1) c 1) ∧
    (NonSplit J a → HasJordanRank J (peirce J c 1) c 2) := by sorry

end JordanStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
