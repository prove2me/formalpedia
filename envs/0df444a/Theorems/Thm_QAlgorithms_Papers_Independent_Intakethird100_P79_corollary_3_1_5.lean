-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P79_corollary_3_1_5
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P79.corollary_3_1_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:21:12.747004+00:00
-- url     : https://prove2.me/theorems/0ae15154-118f-49c9-9ce1-3fd4f6234171
-- title:
--   Smoothness at an idempotent and affine-space stabilizers
-- statement:
--   Let $k$ be algebraically closed of characteristic zero, let $M$ be an irreducible algebraic monoid, and let $e\in M$ be idempotent. Let $M_e=\{x\in M:xe=ex=e\}$ with its reduced closed-subscheme structure. Then
--
--   $$e\text{ is a smooth point of }M\quad\Longleftrightarrow\quad\exists n\in\mathbb N,\ M_e\cong_k\mathbb A_k^n.$$
--
--   The isomorphism is one of varieties, with no compatibility with monoid multiplication required. Dimension zero is allowed. This criterion detects smoothness without a normality or affineness assumption on $M$.
-- source:
--   Local structure of algebraic monoids, arXiv:0709.1255v2, PDF p. 17, Corollary 3.1.5

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

/-- Corollary 3.1.5, PDF p. 17: e is smooth in M exactly when the two-sided
stabilizer is isomorphic as a k-variety to affine space. Dimension zero is allowed;
the isomorphism is not required to preserve the monoid multiplication. -/
theorem corollary_3_1_5 [IsAlgClosed k] [CharZero k]
    (M : KScheme k) [MonObj M] [IsVariety k M] [IrreducibleSpace M.left]
    (e : 𝟙_ (KScheme k) ⟶ M) (he : IsIdempotentPoint M e) :
    IsSmoothPoint M e ↔
      ∃ n : ℕ, Nonempty (stabilizer M e 2 ≅ affineSpace (k := k) n) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P79

end
