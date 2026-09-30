-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_nonzero_regularized_grid_zero_estimate
-- name    : WeierstrassEllipticZeta.nonzero_regularized_grid_zero_estimate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T11:56:25.883738+00:00
-- url     : https://prove2.me/theorems/953d58ed-ea38-4e30-8498-1adffd9f7319
-- title:
--   Grid zero estimate for a nonzero regularized auxiliary function
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical Weierstrass functions $\wp,\zeta$. Fix $\omega,u_1,u_2\in\mathbb C$ satisfying `RegularAuxiliaryGridData`: $J(a,b,c)=au_1+bu_2+c\omega$ is injective on $\mathbb Z^3$, lies in $\Lambda$ exactly when $a=b=0$, and two integer grid points are congruent modulo $\Lambda$ exactly when their first two coordinates agree. Every $J(a,b,c)+u_1/2$ is regular. The data includes the standard finite-grid cardinalities, shifted-grid radius bounds and period translation identities.
--
--   Let $D$ be normalized entire sigma differential data: $\sigma=D.\mathrm{sigma}$ is entire, $\sigma(0)=0$, $\sigma'(0)=1$, and $\sigma'=\zeta\sigma$ off $\Lambda$. Write
--
--   $$\Gamma(a,b,c)=\{iu_1+ju_2+k\omega:0\le i<a,\ 0\le j<b,\ 0\le k<c\},$$
--
--   with integer indices. There is a real $C>0$ such that, for all positive integers $m,\ell,s,q$ with $s\le q$ and $\ell\le m$, and all integers $T\ge3$ satisfying
--
--   $$3C\max\{m(15\ell)^2,q(15\ell)^2\}<Ts^2q,$$
--
--   the following implication holds. Let $(c_{ijk})_{0\le i\le m,\ 0\le j,k\le\ell}$ be any complex array and let $G$ be any nonzero entire function such that, whenever $z,z+u_1/2\notin\Lambda$,
--
--   $$G(z)=\sigma(z)^{15\ell}[2(\wp(u_1/2)-\wp(z))]^{3\ell}
--   \sum_{i,j,k}c_{ijk}(z+u_1/2)^i\wp(z+u_1/2)^j\zeta(z+u_1/2)^k.$$
--
--   Then $G^{(n)}(v)\ne0$ for some $v\in\Gamma(3s,3s,3q)$ and integer $0\le n\le T$.
--
--   The constant is uniform over the five integers, the coefficient array and the entire extension. Nonvanishing of $G$ is an explicit hypothesis; the coefficient array has no separate nonzero or height hypothesis. Entire construction and functional independence are separate steps. The sigma exponent $15\ell$ corresponds to the fixed elliptic homogeneous degree $5\ell$, allowing padding of lower-degree cleared polynomials.
-- source:
--   Senthil Kumar K (2026), proof of Lemma 9 and Appendix Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This inferred form takes the nonzero entire regularized function as input, keeps fixed elliptic homogeneous degree 5ell and sigma exponent 15ell, and preserves the existing sufficient rank-one numerical conditions. The geometric zero estimate remains open.

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.nonzero_regularized_grid_zero_estimate
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ (c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ) (G : ℂ → ℂ),
        AnalyticOnNhd ℂ G Set.univ →
        (∀ w : ℂ, w ∉ L.lattice → w + u₁ / 2 ∉ L.lattice →
          G w = D.sigma w ^ (15 * l) *
            (2 * (L.weierstrassP (u₁ / 2) - L.weierstrassP w)) ^ (3 * l) *
            (∑ i, c i * (w + u₁ / 2) ^ i.1.val *
              L.weierstrassP (w + u₁ / 2) ^ i.2.1.val *
              weierstrassZeta L (w + u₁ / 2) ^ i.2.2.val)) →
        G ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
          ∃ n : ℕ, n ≤ T ∧ iteratedDeriv n G v ≠ 0 := by sorry
