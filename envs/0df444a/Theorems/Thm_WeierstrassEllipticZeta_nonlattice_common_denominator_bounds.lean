-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_nonlattice_common_denominator_bounds
-- name    : WeierstrassEllipticZeta.nonlattice_common_denominator_bounds
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T00:38:13.779899+00:00
-- url     : https://prove2.me/theorems/9fa340d8-2cb6-4ecc-a384-a0668ae6f41f
-- title:
--   Uniform bounds for common elliptic denominators
-- statement:
--   Fix arbitrary complex numbers $\theta,\nu$ and a nonnegative integer $C$. There is a real constant $B>0$, depending only on these three choices, with the following property. Let $L$ be any period pair, $v,z\in\mathbb C$, and $N,s\in\mathbb N$ with $\log N\ge1$. Let $P$ be a `NonlatticeCoordinatePresentation` for the eight coordinates
--
--   $$(z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z)).$$
--
--   Write $p_a,q_a\in\mathbb Z[X,Y]$ for its numerators and denominators, evaluated at $(\theta,\nu)$, and set $E_a=q_a(\theta,\nu)$. The presentation requires $E_a\ne0$ and $p_a(\theta,\nu)=E_a x_a$. Its degree bounds for both numerator and denominator are $C$ in coordinates $0,4,5,6,7$ and $Cs^2$ in coordinates $1,2,3$. Their sums of absolute coefficients are bounded respectively by $e^{C\log N}$, $e^{C(s^2+\log N)}$, and $e^C$ in the ordinary, moving elliptic, and fixed base coordinates.
--
--   The explicitly constructed common denominator
--
--   $$Q=E_1E_2E_3$$
--
--   is nonzero and satisfies
--
--   $$|Q|+|Q\zeta(v)|+|Q\wp(v)|+|Q\wp'(v)|\le e^{B(s^2+\log N)}.$$
--
--   Moreover, simultaneously for all nonnegative integers $m,\ell,n$,
--
--   $$\left|E_0^m(E_4E_5E_6E_7)^{m+5\ell+n}\right|
--   \le e^{B(m\log N+m+5\ell+n)}.$$
--
--   The constant is uniform in the period pair, points, integers, and presentation. Neither transcendence assumptions nor a lower bound for any denominator norm are required. Orders and degree parameters equal to zero are included. These two estimates control the two exact factors of the arithmetic jet denominator: the common moving denominator to the power $5\ell$ and the residual factor displayed above.
-- source:
--   Senthil Kumar K (2026), Lemma 7(a) and the nonlattice case of Lemma 10, especially the bound preceding equation (36), https://doi.org/10.1017/S001309152610145X. This statement derives uniform norm bounds from the mission's eight-coordinate rational presentations, using the explicit product of the three moving denominators; its constants and coordinate profiles are the formalization's quantitative interfaces.

import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.nonlattice_common_denominator_bounds (θ ν : ℂ) (C : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (L : PeriodPair) (v z : ℂ) (N s : ℕ),
      1 ≤ Real.log N → ∀ P : NonlatticeCoordinatePresentation L θ ν v z C N s,
        let E : Fin 8 → ℂ := fun a =>
          MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (P.denominator a)
        let Q := E 1 * E 2 * E 3
        Q ≠ 0 ∧
          ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
              ‖Q * L.derivWeierstrassP v‖ ≤ Real.exp (B * ((s : ℝ) ^ 2 + Real.log N)) ∧
          ∀ m l n : ℕ,
            ‖E 0 ^ m * (E 4 * E 5 * E 6 * E 7) ^ (m + 5 * l + n)‖ ≤
              Real.exp (B * ((m : ℝ) * Real.log N + m + 5 * l + n)) := by sorry
