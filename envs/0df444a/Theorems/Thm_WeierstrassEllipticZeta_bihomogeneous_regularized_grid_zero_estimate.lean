-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bihomogeneous_regularized_grid_zero_estimate
-- name    : WeierstrassEllipticZeta.bihomogeneous_regularized_grid_zero_estimate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T13:52:46.703734+00:00
-- url     : https://prove2.me/theorems/056a4d9e-6161-4568-8a7b-5230ab194fa1
-- title:
--   Geometric zero estimate in bihomogeneous elliptic coordinates
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical functions $\wp,\wp',\zeta$. Fix $\omega,u_1,u_2\in\mathbb C$ satisfying `RegularAuxiliaryGridData`: the integer map $J(a,b,c)=au_1+bu_2+c\omega$ is injective, is in $\Lambda$ exactly when $a=b=0$, and two integer grid points are congruent modulo $\Lambda$ exactly when their first two coordinates agree. Every $J(a,b,c)+u_1/2$ is regular. The data includes the standard finite-grid cardinalities, shifted-grid radius bounds and period-translation formulas.
--
--   Let $D$ be normalized sigma differential data, so $\sigma=D.\mathrm{sigma}$ is entire, $\sigma(0)=0$, $\sigma'(0)=1$, and $\sigma'(z)=\zeta(z)\sigma(z)$ off $\Lambda$. Set
--
--   $$\Gamma(a,b,c)=\{iu_1+ju_2+k\omega:0\le i<a,\ 0\le j<b,\ 0\le k<c\},$$
--
--   where the indices are integers. There is a real $C>0$ such that for all positive integers $m,\ell,s,q$ with $s\le q$ and $\ell\le m$, and all integers $T\ge3$ satisfying
--
--   $$3C\max\{m(15\ell)^2,q(15\ell)^2\}<Ts^2q,$$
--
--   the following holds. Let $Q\in\mathbb C[Y_0,Y_1,X_0,X_1,X_2,X_3,X_4]$ be bihomogeneous of degrees $m,5\ell$: every monomial with nonzero coefficient has total $Y$ degree $m$ and total $X$ degree $5\ell$. Let $G:\mathbb C\to\mathbb C$ be entire and not identically zero, with, for every $z\notin\Lambda$,
--
--   $$G(z)=Q\big(1,z;\sigma(z)^3,\sigma(z)^3\wp(z),\sigma(z)^3\wp'(z),\sigma(z)^3\zeta(z),\sigma(z)^3[\wp'(z)\zeta(z)+2\wp(z)^2]\big).$$
--
--   Then there exist $v\in\Gamma(3s,3s,3q)$ and an integer $0\le n\le T$ such that $G^{(n)}(v)\ne0$.
--
--   The constant is uniform in all five integer parameters, $Q$ and $G$. The nonzero entire function is an explicit input; merely $Q\ne0$ is not substituted for this hypothesis. The final projective coordinate $X_4$ is allowed to occur in $Q$. This is the remaining geometric zero estimate in the full coordinates of the source's algebraic group, and still requires proof.
-- source:
--   Senthil Kumar K (2026), Appendix Theorem A.3, Proposition A.1 and the proof of Lemma 9, https://doi.org/10.1017/S001309152610145X. This inferred specialization uses the full seven coordinates of Ga times the universal vectorial extension of the elliptic curve, exact bidegree (m,5ell), and the existing sufficient grid inequality. The given nonzero entire G agrees with the homogeneous polynomial evaluated in sigma-cubed coordinates off the lattice. The algebraic-group zero estimate, its grid specialization, and the identification of its analytic section with this G remain proof obligations.

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.bihomogeneous_regularized_grid_zero_estimate
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ (Q : MvPolynomial (Fin 7) ℂ) (G : ℂ → ℂ),
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = 5 * l) →
        AnalyticOnNhd ℂ G Set.univ →
        (∀ z : ℂ, z ∉ L.lattice →
          G z = MvPolynomial.eval ![1, z, D.sigma z ^ 3,
            D.sigma z ^ 3 * L.weierstrassP z,
            D.sigma z ^ 3 * L.derivWeierstrassP z,
            D.sigma z ^ 3 * weierstrassZeta L z,
            D.sigma z ^ 3 * (L.derivWeierstrassP z * weierstrassZeta L z +
              2 * L.weierstrassP z ^ 2)] Q) →
        G ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
          ∃ n : ℕ, n ≤ T ∧ iteratedDeriv n G v ≠ 0 := by sorry
