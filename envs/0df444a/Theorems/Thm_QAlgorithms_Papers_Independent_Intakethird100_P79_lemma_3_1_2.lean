-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P79_lemma_3_1_2
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P79.lemma_3_1_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:19:49.254239+00:00
-- url     : https://prove2.me/theorems/ef9e6992-e78c-4350-83f7-3fa6c23aca0c
-- title:
--   Affineness of the three group stabilizers
-- statement:
--   Let $k$ be an algebraically closed field of characteristic zero, let $M$ be an irreducible algebraic monoid with unit group $G$, and let $e\in M$ satisfy $e^2=e$. Define $G_e^\ell=\{g\in G:ge=e\}$, $G_e^r=\{g\in G:eg=e\}$ and $G_e=G_e^\ell\cap G_e^r$. Then
--
--   $$G_e^\ell,\quad G_e^r,\quad G_e\quad\text{are affine algebraic groups}.$$
--
--   No affineness or normality of $M$ is assumed. This gives affine group stabilizers even for non-affine monoids.
--
--   **Formalization Note** The unit group is represented by the inverse-pair scheme $\{(x,y):xy=yx=1\}$, and each stabilizer is computed by equalizer equations, rather than supplied as an arbitrary group.
-- source:
--   Local structure of algebraic monoids, arXiv:0709.1255v2, PDF p. 16, Lemma 3.1.2

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

/-- Lemma 3.1.2, PDF p. 16: all three group stabilizers are affine.
M is arbitrary irreducible; affineness and normality of M are not hypotheses. -/
theorem lemma_3_1_2 [IsAlgClosed k] [CharZero k]
    (M : KScheme k) [MonObj M] [IsVariety k M] [IrreducibleSpace M.left]
    (e : 𝟙_ (KScheme k) ⟶ M) (he : IsIdempotentPoint M e) :
    ∀ side : Fin 3, IsAffine (groupStabilizer M e side).left := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P79

end
