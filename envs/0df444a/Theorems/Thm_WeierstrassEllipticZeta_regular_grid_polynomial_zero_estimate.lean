-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_regular_grid_polynomial_zero_estimate
-- name    : WeierstrassEllipticZeta.regular_grid_polynomial_zero_estimate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T01:38:17.437713+00:00
-- url     : https://prove2.me/theorems/fb45598a-28e6-4e3f-8d37-3f2f69a2d34b
-- title:
--   Polynomial zero estimate on a regular elliptic grid
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical Weierstrass functions $\wp,\zeta$. Fix $\omega,u_1,u_2\in\mathbb C$ satisfying `RegularAuxiliaryGridData`: the map $J(a,b,c)=au_1+bu_2+c\omega$ on $\mathbb Z^3$ is injective; $J(a,b,c)\in\Lambda$ exactly when $a=b=0$; two integer grid points are congruent modulo $\Lambda$ exactly when their first two coordinates coincide; and every $J(a,b,c)+u_1/2$ lies outside $\Lambda$. The data also includes the finite-grid cardinality, shifted-grid regularity and radius bounds, and the period translation formulas for $\wp,\wp'$ and $\zeta$.
--
--   For positive integers $a,b,c$, write
--
--   $$\Gamma(a,b,c)=\{iu_1+ju_2+k\omega:0\le i<a,\ 0\le j<b,\ 0\le k<c\},$$
--
--   with integer indices. There is a real constant $C>0$ such that the following holds for all positive integers $m,\ell,s,q$, with $s\le q$ and $\ell\le m$, and all integers $T\ge3$. If
--
--   $$3C\max\{m(15\ell)^2,\ q(15\ell)^2\}<T s^2q,$$
--
--   then every nonzero complex coefficient array $(c_{ijk})_{0\le i\le m,\ 0\le j,k\le\ell}$ gives a function
--
--   $$F_c(w)=\sum_{i=0}^{m}\sum_{j=0}^{\ell}\sum_{k=0}^{\ell}c_{ijk}w^i\wp(w)^j\zeta(w)^k$$
--
--   with $F_c^{(n)}(u_1/2+v)\ne0$ for some $v\in\Gamma(3s,3s,3q)$ and integer $0\le n\le T+6\ell$.
--
--   The constant is uniform in the five integer parameters and the coefficient array. There is no coefficient-height bound or initial-vanishing hypothesis. All evaluation points are regular. This statement combines functional nonvanishing, cleared translation, and the geometric zero estimate; it makes no claim about the magnitude of the selected derivative.
-- source:
--   Senthil Kumar K (2026), proof of Lemma 9 and Appendix Proposition A.1 with kappa=1, https://doi.org/10.1017/S001309152610145X. This is the translated-function consequence, inferred from functional algebraic independence, the degree bounds D0<=m and D2<=5ell, and the possible order loss 6ell at lattice points. The geometric zero estimate and functional nonvanishing remain proof obligations.

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.regular_grid_polynomial_zero_estimate
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        c ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
          ∃ n : ℕ, n ≤ T + 6 * l ∧
            iteratedDeriv n (fun w => ∑ i, c i * w ^ i.1.val *
              L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
                (u₁ / 2 + v) ≠ 0 := by sorry
