-- Prove2me | Theorems.Thm_WeierstrassCurve_valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt
-- name    : WeierstrassCurve.valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/ddec431c-27e3-5a96-aac6-47d6f6c30b41
-- title:
--   Levels of odd ℓ-torsion reducing to a node
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and $q$ a prime with $W.\Delta \neq 0$, $q \mid W.\Delta$ and $q \nmid W.c_4$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$ (the predicate `LiesOverPrime`, i.e. $q$ lies in `A.nonunits`), and write $v$ for `A.valuation`. Let $x_0, y_0 \in A$ satisfy the two partial-derivative equations $2y_0 + a_1x_0 + a_3 = 0$ and $a_1y_0 = 3x_0^2 + 2a_2x_0 + a_4$, together with $v(b_2 + 12x_0) = 1$ and $v(F_0) < 1$, where $F_0 = y_0^2 + a_1x_0y_0 + a_3y_0 - (x_0^3 + a_2x_0^2 + a_4x_0 + a_6)$. Let $\ell$ be a prime with $\ell \neq 2$, and let $(x,y)$ be a nonsingular point of the affine equation of $W$ base changed to $\overline{\mathbb{Q}}$, such that the corresponding point `Point.some x y h` is killed by $\ell$ and satisfies $v(x - x_0) < 1$. Then $v(W.\Delta) < v(x - x_0)^2$, and there is a natural number $j$ with $1 \le j$ and $2j < \ell$ such that $v(x - x_0)^{\ell} = v(W.\Delta)^{j}$. (Valuations are written multiplicatively, so $v(\cdot) < 1$ means positive valuation.)
--
--   This is the determination of the possible levels $v(x-x_0)$ of $\ell$-torsion points reducing to the node of a multiplicative reduction: on the Tate parametrisation of a curve of reduction type $I_n$, such levels are the fractions $j\,v(\Delta)/\ell$ with $1 \le j \le (\ell-1)/2$, and in particular no $\ell$-torsion point other than those in the identity component reduces to the node with level $\ge v(\Delta)^{1/2}$. It is a variant of the torsion-level theorem that does not assume $\ell \neq q$, so it may also be applied to $q$-torsion at a place above $q$; it is used in the analysis of which torsion points lie in the identity component at $A$ and in the valuation computation for products of Velu coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (htor : ℓ • (Point.some x y h) = 0) (hX : A.valuation (x - x₀) < 1) :
    A.valuation (W.Δ : AlgebraicClosure ℚ) < A.valuation (x - x₀) ^ 2 ∧
      ∃ j : ℕ, 1 ≤ j ∧ 2 * j < ℓ ∧
        A.valuation (x - x₀) ^ ℓ = A.valuation (W.Δ : AlgebraicClosure ℚ) ^ j := by sorry
