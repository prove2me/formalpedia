-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_regular_grid_sigma_zero_estimate
-- name    : WeierstrassEllipticZeta.regular_grid_sigma_zero_estimate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T02:10:58.355333+00:00
-- url     : https://prove2.me/theorems/ebabd378-a5ce-4ad8-80eb-d79265dd0ff7
-- title:
--   Nonzero derivative of the sigma-regularized auxiliary function
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical Weierstrass functions $\wp,\zeta$. Fix $\omega,u_1,u_2\in\mathbb C$ satisfying `RegularAuxiliaryGridData`: the integer map $J(a,b,c)=au_1+bu_2+c\omega$ is injective, belongs to $\Lambda$ exactly when $a=b=0$, and two integer grid points are congruent modulo $\Lambda$ exactly when their first two coordinates agree. Every $J(a,b,c)+u_1/2$ is regular. The data includes the standard finite-grid cardinalities, shifted-grid radius bounds and period translation formulas.
--
--   Let $D$ be normalized entire sigma differential data: $\sigma=D.\mathrm{sigma}$ is entire, $\sigma(0)=0$, $\sigma'(0)=1$, and $\sigma'(z)=\zeta(z)\sigma(z)$ off $\Lambda$. Define
--
--   $$\Gamma(a,b,c)=\{iu_1+ju_2+k\omega:0\le i<a,\ 0\le j<b,\ 0\le k<c\},$$
--
--   with integer indices. There exists a real $C>0$ such that the following holds for all positive integers $m,\ell,s,q$ with $s\le q$ and $\ell\le m$, and all $T\ge3$ satisfying
--
--   $$3C\max\{m(15\ell)^2,q(15\ell)^2\}<Ts^2q.$$
--
--   For every nonzero complex array $(c_{ijk})_{0\le i\le m,\ 0\le j,k\le\ell}$, put
--
--   $$F_c(z)=\sum_{i=0}^{m}\sum_{j=0}^{\ell}\sum_{k=0}^{\ell}
--   c_{ijk}(z+u_1/2)^i\wp(z+u_1/2)^j\zeta(z+u_1/2)^k.$$
--
--   There exists an entire function $G:\mathbb C\to\mathbb C$ such that, whenever $z,z+u_1/2\notin\Lambda$,
--
--   $$G(z)=\sigma(z)^{15\ell}[2(\wp(u_1/2)-\wp(z))]^{3\ell}F_c(z),$$
--
--   and $G^{(n)}(v)\ne0$ for some $v\in\Gamma(3s,3s,3q)$ and integer $0\le n\le T$.
--
--   The constant is uniform in the five integers and the coefficient array. No coefficient-height bound or initial-vanishing condition is assumed. The exponent $15\ell$ corresponds to choosing the fixed elliptic homogeneous degree $5\ell$; padding a lower-degree polynomial is allowed. This is the entire-function zero estimate. The construction and functional nonvanishing of $G$, and the geometric zero estimate yielding the derivative, remain proof obligations.
-- source:
--   Senthil Kumar K (2026), proof of Lemma 9 and Appendix Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This inferred formulation fixes elliptic homogeneous degree 5ell and hence the sigma exponent 15ell, padding lower-degree cleared polynomials. It keeps the existing sufficient rank-one numerical inequalities. Entire regularization, functional nonvanishing and the geometric zero estimate are still to be proved for this statement.

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.regular_grid_sigma_zero_estimate
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        c ≠ 0 → ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G Set.univ ∧
          (∀ w : ℂ, w ∉ L.lattice → w + u₁ / 2 ∉ L.lattice →
            G w = D.sigma w ^ (15 * l) *
              (2 * (L.weierstrassP (u₁ / 2) - L.weierstrassP w)) ^ (3 * l) *
              (∑ i, c i * (w + u₁ / 2) ^ i.1.val *
                L.weierstrassP (w + u₁ / 2) ^ i.2.1.val *
                weierstrassZeta L (w + u₁ / 2) ^ i.2.2.val)) ∧
          ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
            ∃ n : ℕ, n ≤ T ∧ iteratedDeriv n G v ≠ 0 := by sorry
