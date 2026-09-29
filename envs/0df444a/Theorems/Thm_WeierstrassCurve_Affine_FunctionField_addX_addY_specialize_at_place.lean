-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place
-- name    : WeierstrassCurve.Affine.FunctionField.addX_addY_specialize_at_place
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/f58c5978-d547-516d-a9e3-289d999f1464
-- title:
--   Chord formulas on generic points specialise to the group law
-- statement:
--   Let $F$ be an algebraically closed field of characteristic zero with decidable equality, let $W$ be an affine Weierstrass curve over $F$ which is elliptic, and fix decidable equality on its function field $K = W.\mathrm{FunctionField}$. Write $x$ for the image of $X$ under $F[X] \to W.\mathrm{CoordinateRing} \to K$ and $y$ for the image of $Y \in W.\mathrm{CoordinateRing}$ in $K$, and let $W_K$ denote the base change of $W$ along $F \to K$. Let $\varphi_1, \varphi_2$ be $F$-algebra endomorphisms of $K$, and set $x_i = \varphi_i(x)$, $y_i = \varphi_i(y)$, $\lambda = \mathrm{slope}_{W_K}(x_1,x_2,y_1,y_2)$, $x_3 = \mathrm{addX}_{W_K}(x_1,x_2,\lambda)$, $y_3 = \mathrm{addY}_{W_K}(x_1,x_2,y_1,\lambda)$. Assume it is not the case that both $x_1 = x_2$ and $y_1 = \mathrm{negY}_{W_K}(x_2,y_2)$, and that $x_3$ is not the image of any $c \in F$. Let $v$ be a place of $K$ over $F$, that is, a valuation subring $\mathcal{O}_v \subsetneq K$ containing the image of $F$ and whose ring is a principal ideal ring, with $\mathrm{ord}_v$ the negative logarithm of the associated adic valuation. Let $Q_1, Q_2$ be $F$-points of $W$ such that for $i = 1,2$: if $Q_i = 0$ then $x_i \notin \mathcal{O}_v$, and if $Q_i = (a,b)$ with $(a,b)$ nonsingular then $\mathrm{ord}_v(x_i - a) > 0$ and $\mathrm{ord}_v(y_i - b) > 0$. Then the same holds for the sum: if $Q_1 + Q_2 = 0$ then $x_3 \notin \mathcal{O}_v$, and if $Q_1 + Q_2 = (a,b)$ with $(a,b)$ nonsingular then $\mathrm{ord}_v(x_3 - a) > 0$ and $\mathrm{ord}_v(y_3 - b) > 0$.
--
--   This is the statement that the rational chord-and-tangent addition formulas, applied to the two $K$-points of $W$ obtained from a pair of $F$-algebra endomorphisms of the function field, are compatible with reduction at an arbitrary place of $K/F$, including the places where the formulas degenerate (an input at a pole, a vertical chord, or the tangent case). It is used in the construction of dual endomorphism data for isogenies, in [`WeierstrassCurve.Affine.IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong`](thm.html#WeierstrassCurve.Affine.IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.FunctionField.addX_addY_specialize_at_place
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] [DecidableEq W.FunctionField]
    (φ₁ φ₂ : W.FunctionField →ₐ[F] W.FunctionField)
    (hcol : ¬ (φ₁ (polyToFunctionField W Polynomial.X) = φ₂ (polyToFunctionField W Polynomial.X) ∧
      φ₁ (yCoord W) = (W.map (algebraMap F W.FunctionField)).toAffine.negY
        (φ₂ (polyToFunctionField W Polynomial.X)) (φ₂ (yCoord W))))
    (hnc : ∀ c : F,
      (W.map (algebraMap F W.FunctionField)).toAffine.addX
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        ≠ algebraMap F W.FunctionField c)
    (v : AlgebraicCurve.Place F W.FunctionField) (Q₁ Q₂ : W.Point)
    (h₁0 : Q₁ = 0 → φ₁ (polyToFunctionField W Polynomial.X) ∉ v.toValuationSubring)
    (h₁s : ∀ (a b : F) (h : W.Nonsingular a b), Q₁ = .some a b h →
      0 < v.ord (φ₁ (polyToFunctionField W Polynomial.X) - algebraMap F W.FunctionField a) ∧
        0 < v.ord (φ₁ (yCoord W) - algebraMap F W.FunctionField b))
    (h₂0 : Q₂ = 0 → φ₂ (polyToFunctionField W Polynomial.X) ∉ v.toValuationSubring)
    (h₂s : ∀ (a b : F) (h : W.Nonsingular a b), Q₂ = .some a b h →
      0 < v.ord (φ₂ (polyToFunctionField W Polynomial.X) - algebraMap F W.FunctionField a) ∧
        0 < v.ord (φ₂ (yCoord W) - algebraMap F W.FunctionField b)) :
    (Q₁ + Q₂ = 0 →
      (W.map (algebraMap F W.FunctionField)).toAffine.addX
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        ∉ v.toValuationSubring) ∧
    (∀ (a b : F) (h : W.Nonsingular a b), Q₁ + Q₂ = .some a b h →
      0 < v.ord ((W.map (algebraMap F W.FunctionField)).toAffine.addX
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        - algebraMap F W.FunctionField a) ∧
      0 < v.ord ((W.map (algebraMap F W.FunctionField)).toAffine.addY
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          (φ₁ (yCoord W))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        - algebraMap F W.FunctionField b)) := by sorry
