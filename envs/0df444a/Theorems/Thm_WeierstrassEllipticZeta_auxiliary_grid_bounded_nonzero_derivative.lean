-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_auxiliary_grid_bounded_nonzero_derivative
-- name    : WeierstrassEllipticZeta.auxiliary_grid_bounded_nonzero_derivative
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T01:13:51.297735+00:00
-- url     : https://prove2.me/theorems/0bdb0578-5437-40c2-828d-92f84806a042
-- title:
--   A bounded nonzero derivative on the enlarged auxiliary grid
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical Weierstrass functions $\wp,\zeta$. Let $\omega,u_1,u_2\in\mathbb C$ satisfy `RegularAuxiliaryGridData`: the integer map
--
--   $$J(a,b,c)=au_1+bu_2+c\omega$$
--
--   is injective; $J(a,b,c)$ lies in $\Lambda$ exactly when $a=b=0$; two integer points are congruent modulo $\Lambda$ exactly when their first two coordinates agree; and every $J(a,b,c)+u_1/2$ is outside $\Lambda$. The data also includes the standard finite-grid cardinality, shifted-grid regularity and radius estimates, and period-translation formulas for $\wp,\wp'$ and $\zeta$.
--
--   Define the unshifted rectangular grid
--
--   $$\Gamma(A,B,C)=\{au_1+bu_2+c\omega:0\le a<A,\ 0\le b<B,\ 0\le c<C\},$$
--
--   with integer indices, and put
--
--   $$m_N=\lfloor N/\log N\rfloor,\quad \ell_N=\lfloor\sqrt{N\log N}\rfloor,\quad
--   s_N=\lfloor N^{3/16}\rfloor,\quad q_N=\lfloor N^{5/8}\log N/64\rfloor.$$
--
--   There is an integer $K\ge1$ such that, for every sufficiently large integer $N$ and every nonzero coefficient vector $c=(c_{ijk})\in\mathbb C^{\{0,\ldots,m_N\}\times\{0,\ldots,\ell_N\}^2}$, the function
--
--   $$F_c(w)=\sum_{i=0}^{m_N}\sum_{j=0}^{\ell_N}\sum_{k=0}^{\ell_N}
--   c_{ijk}w^i\wp(w)^j\zeta(w)^k$$
--
--   has a nonzero derivative $F_c^{(n)}(u_1/2+v)$ for some $v\in\Gamma(3s_N,3s_N,3q_N)$ and some integer $0\le n\le Km_N$. The constant and the threshold are uniform in the coefficient vector. No size bound or initial vanishing condition is imposed on the coefficients. All evaluation points are regular by the grid hypotheses.
--
--   This is the bounded-order zero estimate needed in the auxiliary construction. It does not assert an upper bound on the magnitude of the selected derivative. The analytic estimates and arithmetic construction are separate proved steps.
-- source:
--   Senthil Kumar K (2026), Section 5, Lemma 9 and its proof using the algebraic independence of z, wp(z), zeta(z) and the appendix zero estimate A.1, https://doi.org/10.1017/S001309152610145X. The formulation is uniform over all nonzero complex coefficient vectors; it isolates the zero estimate used before the arithmetic size argument.

import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem

open scoped Polynomial
open Filter WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.auxiliary_grid_bounded_nonzero_derivative
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        c ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω
          ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
          ∃ n : ℕ, n ≤ K * m ∧
            iteratedDeriv n (fun w => ∑ i, c i * w ^ i.1.val *
              L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
                (u₁ / 2 + v) ≠ 0 := by sorry
