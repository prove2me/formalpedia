-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_poincare_semidirect_isometry_algebra
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.poincare_semidirect_isometry_algebra
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:10:31.736814+00:00
-- url     : https://prove2.me/theorems/7febb676-249b-4fb1-8ec9-018418381ac6
-- title:
--   Section 1.1: Poincare semidirect structure and isometry algebra
-- statement:
--   Equip $V=\mathbb R^{p,q}$ with its standard metric and write $\mathfrak{so}(V)=\{A:A^Tg+gA=0\}$. The vector space $\mathfrak{so}(V)\oplus V$ is closed under the bilinear bracket
--   $$[(A,v),(B,w)]=(AB-BA,Aw-Bv).$$
--   This bracket is skew and satisfies Jacobi. The translation subspace is an abelian ideal, and the orthogonal algebra acts on it by the standard action $w\mapsto Aw$. This is the Lie algebra of the full metric-isometry group: every interval-preserving bijection of $V$ is affine $x\mapsto Ax+b$ with $A^TgA=g$, and all such affine maps occur. Its tangent vectors at the identity are exactly the indicated pairs $(A,v)$, where tangent membership is represented by derivatives of smooth curves in the actual affine-isometry coefficient set. This provides the semidirect structure without adding claims about Levi decomposition or causal cones.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 6, Section 1.1: Poincare semidirect structure and isometry algebra

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Section 1.1, PDF p. 6: the complete semidirect/standard-action statement and the
isometry Lie algebra. The latter uses actual smooth group curves. No assertion
about a radical, reductivity, or causal cones is added. -/
theorem poincare_semidirect_isometry_algebra (p q : ℕ) :
    (∀ z : Matrix (Fin (p + q)) (Fin (p + q)) ℝ × (Fin (p + q) → ℝ),
      z ∈ poincareSpace p q ↔ IsometryVelocity p q z) ∧
    (∀ x y, x ∈ poincareSpace p q → y ∈ poincareSpace p q →
      poincareBracket x y ∈ poincareSpace p q) ∧
    (∀ x y : Matrix (Fin (p + q)) (Fin (p + q)) ℝ × (Fin (p + q) → ℝ),
      poincareBracket x y = -poincareBracket y x) ∧
    (∀ x y z : Matrix (Fin (p + q)) (Fin (p + q)) ℝ × (Fin (p + q) → ℝ),
      poincareBracket x (poincareBracket y z) + poincareBracket y (poincareBracket z x) +
        poincareBracket z (poincareBracket x y) = 0) ∧
    (∀ v w : (Fin (p + q) → ℝ), poincareBracket (0, v) (0, w) = (0, 0)) ∧
    (∀ (A : orthogonalSpace p q) (v w : (Fin (p + q) → ℝ)),
      poincareBracket (A.val, v) (0, w) = (0, A.val.mulVec w)) ∧
    (∀ f : (Fin (p + q) → ℝ) ≃ (Fin (p + q) → ℝ),
      (∀ x y, (signatureMatrix p q).toBilin' (f x - f y) (f x - f y) =
        (signatureMatrix p q).toBilin' (x - y) (x - y)) →
      ∃ (A : Matrix (Fin (p + q)) (Fin (p + q)) ℝ) (b : (Fin (p + q) → ℝ)),
        AffineIsometryCoefficients p q A ∧ ∀ x, f x = A.mulVec x + b) ∧
    (∀ (A : Matrix (Fin (p + q)) (Fin (p + q)) ℝ) (b : (Fin (p + q) → ℝ)),
      AffineIsometryCoefficients p q A →
      ∃ f : metricIsometryGroup p q, ∀ x, f.val x = A.mulVec x + b) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
