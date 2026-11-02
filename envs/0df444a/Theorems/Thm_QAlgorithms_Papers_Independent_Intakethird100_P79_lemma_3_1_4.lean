-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P79_lemma_3_1_4
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P79.lemma_3_1_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:20:32.253198+00:00
-- url     : https://prove2.me/theorems/a1ccb6ff-ada9-4832-9843-a7a9b519211e
-- title:
--   Affine connected stabilizers with dense unit groups
-- statement:
--   Let $k$ be algebraically closed of characteristic zero, let $M$ be an irreducible algebraic monoid with unit group $G$, and let $e\in M$ be idempotent. Give $M_e^\ell=\{x\in M:xe=e\}$, $M_e^r=\{x\in M:ex=e\}$ and $M_e=M_e^\ell\cap M_e^r$ their reduced closed-subscheme structures. For $s\in\{\ell,r,\mathrm{two}\}$, write $S_s$ for the respective stabilizer and $G_s=G\cap S_s$ for its unit group. Then
--
--   $$\forall s\in\{\ell,r,\mathrm{two}\},\qquad S_s\text{ is affine and connected},\qquad\overline{G_s}^{\,M}=S_s.$$
--
--   The closure formula states density of each actual unit group in its own stabilizer. It does not assert irreducibility, and requires neither affineness nor normality of $M$.
-- source:
--   Local structure of algebraic monoids, arXiv:0709.1255v2, PDF p. 17, Lemma 3.1.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P79

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

open CategoryTheory.MonObj

open scoped CategoryTheory.MonObj Pointwise

universe u

namespace QAlgorithms.Papers.Independent.Intakethird100.P79

variable (k : Type u) [Field k]

variable {k}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Lemma 3.1.4, PDF p. 17: the three reduced stabilizers are affine and
connected, and their actual unit groups are dense. Closure is taken inside M,
and is compared with the canonical stabilizer inclusion, so density is not input. -/
theorem lemma_3_1_4 [IsAlgClosed k] [CharZero k]
    (M : KScheme k) [MonObj M] [IsVariety k M] [IrreducibleSpace M.left]
    (e : 𝟙_ (KScheme k) ⟶ M) (he : IsIdempotentPoint M e) :
    ∀ side : Fin 3,
      IsAffine (stabilizer M e side).left ∧
      ConnectedSpace (stabilizer M e side).left ∧
      closure (Set.range (groupStabilizerInclusion M e side).left) =
        Set.range (stabilizerInclusion M e side).left := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P79

end
