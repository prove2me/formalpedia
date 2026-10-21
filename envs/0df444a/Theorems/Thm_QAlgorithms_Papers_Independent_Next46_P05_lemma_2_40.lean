-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_2_40
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_2_40
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:50:31.207994+00:00
-- url     : https://prove2.me/theorems/36973485-29a3-4c20-be5a-406018ebe82f
-- title:
--   Lemma 2.40: stable corners have even rank in the non-split case
-- statement:
--   Let $V$ be a finite-dimensional real unital euclidean Jordan algebra, with bilinear Jordan product, unit $e$, and a positive definite associative scalar product. Assume $V$ is simple, and $\alpha$ is an involutive Jordan automorphism with $2\operatorname{rank}V^\alpha=\operatorname{rank}V$. Let $F=(c_1,\ldots,c_r)$ be a Jordan frame with $\alpha(F)=F$. For $1\le k\le r$, if the corner $V_1(c_1+\cdots+c_k)$ is $\alpha$-invariant, then
--
--   $$k\text{ is even}.$$
--
--   Frame stability and corner stability are distinct hypotheses; the full corner $k=r$ is included. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 17, Lemma 2.40

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

/-- Lemma 2.40, PDF p. 17. Frame stability and partial-algebra stability are separate. -/
theorem lemma_2_40 (J : EuclideanJordan V) (hs : SimpleJordanIn J ⊤)
    (a : JordanAuto J) (ha : Function.Involutive a.linear) (hn : NonSplit J a)
    {r : ℕ} (c : Fin r → V) (hf : JordanFrame J c)
    (hstable : a.linear '' Set.range c = Set.range c) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ r)
    (hsub : ∀ x ∈ peirce J (partialUnit c k) 1,
      a.linear x ∈ peirce J (partialUnit c k) 1) : Even k := by sorry

end JordanStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
