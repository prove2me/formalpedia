-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_sigma_regularized_coordinates_entire
-- name    : WeierstrassEllipticZeta.sigma_regularized_coordinates_entire
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T22:20:33.834016+00:00
-- url     : https://prove2.me/theorems/80ccd116-e1e7-4a70-96fa-93e5f0e7c0ce
-- title:
--   Entire sigma factors and transfer of quadratic exponential bounds
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical Weierstrass functions $\zeta,\wp,\wp'$. Let $\sigma$ be an entire function satisfying
--
--   $$\sigma(0)=0,\qquad \sigma'(0)=1,\qquad
--   \sigma'(z)=\zeta(z)\sigma(z)\quad(z\notin\Lambda).$$
--
--   Assume $\zeta'(z)=-\wp(z)$ outside the lattice. There exist three entire functions $S_0,S_1,S_2$ such that
--
--   $$S_0(z)=\sigma(z)\zeta(z),\qquad
--   S_1(z)=\sigma(z)^2\wp(z),\qquad
--   S_2(z)=\sigma(z)^3\wp'(z)\quad(z\notin\Lambda),$$
--
--   and
--
--   $$S_0(0)=1,\qquad S_1(0)=1,\qquad S_2(0)=-2.$$
--
--   The same three functions preserve finite quadratic exponential bounds. For every real $A\ge0$, if
--
--   $$|\sigma(z)|\le \exp\bigl(A(1+|z|^2)\bigr)\qquad(z\in\mathbb C),$$
--
--   then
--
--   $$|S_j(z)|\le \exp\bigl((9A+24)(1+|z|^2)\bigr)
--   \qquad(z\in\mathbb C,\ j=0,1,2).$$
--
--   The factors are chosen before $A$ or any bound. Their entire extensions include lattice points, where they need not equal products of totalized meromorphic values. The result supplies the pole-clearing factors needed by Kumar's auxiliary-function regularization. Existence of a finite quadratic exponential bound for $\sigma$ itself is a separate assertion.
-- source:
--   Senthil Kumar K (2026), Section 4, entire-function assertion after equation (15) and before Lemma 6, https://doi.org/10.1017/S001309152610145X. Differential identities: DLMF 23.2.7–23.2.8, https://dlmf.nist.gov/23.2. The explicit bound 9A+24 is a coarse formalization consequence of the unit-circle Cauchy estimate.

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization

open WeierstrassEllipticZeta Set

theorem WeierstrassEllipticZeta.sigma_regularized_coordinates_entire (L : PeriodPair)
    (D : EllipticSigmaDifferentialData L)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z) :
    ∃ S : Fin 3 → ℂ → ℂ,
      (∀ j, AnalyticOnNhd ℂ (S j) univ) ∧
      (∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
        S j z = D.sigma z ^ (j.val + 1) * ellipticPoleCoordinates L z j) ∧
      S 0 0 = 1 ∧ S 1 0 = 1 ∧ S 2 0 = -2 ∧
      ∀ A : ℝ, 0 ≤ A →
        (∀ z : ℂ, ‖D.sigma z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2))) →
        ∀ (z : ℂ) (j : Fin 3),
          ‖S j z‖ ≤ Real.exp ((9 * A + 24) * (1 + ‖z‖ ^ 2)) := by sorry
