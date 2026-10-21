-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_generated_and_central_projectors
-- name    : QAlgorithms.Papers.Independent.Support21.P08.generated_and_central_projectors
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:34:40.551669+00:00
-- url     : https://prove2.me/theorems/de051cd4-46b1-4a3d-92f4-b0ab280eba54
-- title:
--   Generated projectors and the central regular-module consequence
-- statement:
--   Let $R$ be a commutative integral domain, and let $L_1,\ldots,L_n$ be upper triangular matrices on a chosen basis indexed by $\{1,\ldots,d\}$. Write $r_k^i$ for the $i$th diagonal entry of $L_k$. A matrix has shape $J$ when its diagonal is the indicator of the nonempty set $J$ and every nonzero entry at $(a,b)$ has $a\le i\le b$ for some $i\in J$. Assume $R$ is local. The complete class-shaped orthogonal projectors can be chosen in $R[L_1,\ldots,L_n]$ in the matrix image. For the left regular module of an algebra $A$, if all JM elements are central, there are corresponding central projectors in the original algebra, satisfying
--
--   $$e_ae_b=\delta_{ab}e_a,\qquad\sum_a e_a=1_A.$$
--
--   When $R$ is a field, every primitive central block is supported on exactly one class projector, so the block decomposition refines linkage. A nonfaithful representation alone is never used to pull matrix idempotents back.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 28, App.6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section AppendixDefinitions

variable {R : Type*} [CommRing R]

/-- Appendix Remark 6.2, PDF pp.28–29, including the central regular case.
The first clause is in the matrix image. For algebra-level projectors a regular
basis is required. Primitive central blocks refine the class decomposition,
expressed by the unique class idempotent supporting each primitive central p.
No claim is made about the literal erroneous nonsingleton interpolation. -/
theorem generated_and_central_projectors [IsDomain R] [IsLocalRing R] :
    (∀ (d n : ℕ) (S : TriangularSystem R d n),
      ∃ e : Finset (Fin d) → Matrix (Fin d) (Fin d) R, ClassProjectors S e) ∧
    (∀ (A : Type*) [Ring A] [Algebra R A] (d n : ℕ)
      (b : Module.Basis (Fin d) R A) (L : Fin n → A)
      (hupper : ∀ k i j, j < i → regularMatrix b (L k) i j = 0),
      (∀ k, Central (L k)) →
      ∃ e : Finset (Fin d) → A,
        (∀ J ∈ linkagePartition (regularSystem b L hupper),
          e J ∈ Algebra.adjoin R (Set.range L) ∧ Central (e J) ∧ e J * e J = e J ∧
          HasShape (regularMatrix b (e J)) J) ∧
        (∀ J ∈ linkagePartition (regularSystem b L hupper),
          ∀ U ∈ linkagePartition (regularSystem b L hupper), J ≠ U → e J * e U = 0) ∧
        (∑ J ∈ linkagePartition (regularSystem b L hupper), e J = 1) ∧
        (IsField R → ∀ p : A, PrimitiveCentralIdempotent p →
          ∃! J : {J // J ∈ linkagePartition (regularSystem b L hupper)}, e J.val * p = p)) := by sorry

end AppendixDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
