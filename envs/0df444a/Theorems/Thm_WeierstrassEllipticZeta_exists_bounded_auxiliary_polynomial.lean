-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exists_bounded_auxiliary_polynomial
-- name    : WeierstrassEllipticZeta.exists_bounded_auxiliary_polynomial
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T00:18:17.818164+00:00
-- url     : https://prove2.me/theorems/bffad94a-0744-4ceb-8fca-334873eec7c8
-- title:
--   Lemma 8: a bounded auxiliary polynomial with prescribed zeros
-- statement:
--   This is the bounded auxiliary-polynomial statement associated with [Senthil Kumar (2026), Lemma 8](https://doi.org/10.1017/S001309152610145X), using the following explicit variant with the mission's established grid parameters.
--
--   Fix a complex period pair $L$, its canonical functions $\wp,\zeta$, and $\omega,u_1,u_2$ with `RegularAuxiliaryGridData`: the integer map $J(a,b,c)=au_1+bu_2+c\omega$ is injective, $J(a,b,c)$ is a period exactly when $a=b=0$, congruence modulo the lattice is determined by the first two coordinates, and every $J(a,b,c)+u_1/2$ is regular. The grid data also include the usual cardinality, radius and period-translation identities.
--
--   Fix an arithmetic model $\theta,\nu\in\mathbb C$, with $\theta$ transcendental over $\mathbb Q$, and a monic $g(X,Y)\in\mathbb Z[X,Y]$ of positive $Y$-degree $e$ such that, for every integer bivariate polynomial $A$,
--   $$A(\theta,\nu)=0\quad\Longleftrightarrow\quad g\mid A.$$
--   Let $d\in\mathbb Z[X]$ and $\delta=d(\theta)\ne0$. Each of the following 18 values must admit a presentation $A_x(\theta,\nu)=\delta x$ with $\deg_Y A_x<e$:
--   $$g_2/4,g_3/4,\omega,\eta(\omega),u_1/2,u_2,\zeta(u_1/2),\wp(u_1/2),\wp'(u_1/2),\wp''(u_1/2),$$
--   $$\wp(u_j),\wp'(u_j),\wp''(u_j),\zeta(u_j)\qquad(j=1,2).$$
--
--   Put
--   $$m=\lfloor N/\log N\rfloor,\quad \ell=\lfloor\sqrt{N\log N}\rfloor,\quad s=\lfloor N^{3/16}\rfloor,\quad q=\lfloor N^{5/8}\log N/64\rfloor,$$
--   and write $\Gamma(a,b,c)=\{iu_1+ju_2+k\omega:0\le i<a,\ 0\le j<b,\ 0\le k<c\}$ with integer indices.
--
--   There are constants $C>0$ and $N_0$, depending only on the fixed lattice, grid generators and arithmetic model, such that for every integer $N\ge N_0$ there are polynomials $A_{ijk}(X,Y)\in\mathbb Z[X,Y]$, indexed by $0\le i\le m$ and $0\le j,k\le\ell$, satisfying
--   $$\deg_Y A_{ijk}<e,\qquad \deg_X A_{ijk}\le Cm,\qquad |[X^aY^b]A_{ijk}|\le e^{CN}.$$
--   Their evaluations $c_{ijk}=A_{ijk}(\theta,\nu)$ must not all be zero, and the polynomial
--   $$P(X_1,X_2,X_3)=\sum_{i,j,k}c_{ijk}X_1^iX_2^jX_3^k$$
--   must yield
--   $$\left.\frac{d^t}{dz^t}P(z+u_1/2,\wp(z+u_1/2),\zeta(z+u_1/2))\right|_{z=v}=0$$
--   for every $v\in\Gamma(s,s,q)$ and $0\le t\le m$.
--
--   Scope of the variant: the paper chooses a suitable constant in its third grid side and imposes vanishing at nonperiod grid points. This target fixes the already-established constant $1/64$ and requires vanishing on the whole smaller shifted grid, whose points are all regular. The coefficient bounds retain the required $O(N/\log N)$ degree and $O(N)$ logarithmic-height scales.
--
--
--   The formal statement encodes the polynomial by its rectangular coefficient family. It states the derivative vanishing for the unshifted function at $u_1/2+v$; translation invariance of iterated derivatives gives the displayed shifted-function formulation. Nonvanishing is explicitly after arithmetic evaluation. Only the lattice/grid and fixed arithmetic-model hypotheses are assumed.
-- source:
--   Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://doi.org/10.1017/S001309152610145X, §5, Lemmas 7–8 and equation (29); mission Lemma 8 formal-grid variant with factor 1/64.

import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Mathlib.RingTheory.Algebraic.Defs

open scoped Polynomial
open Filter WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.exists_bounded_auxiliary_polynomial
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (ν : ℂ)
    (g : ℤ[X][X]) (hg_monic : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_kernel : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.natDegree < g.natDegree ∧
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∃ p : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℤ[X][X],
        (fun i => (p i).eval₂ (Polynomial.aeval θ).toRingHom ν) ≠ 0 ∧
        (∀ i, (p i).natDegree < g.natDegree) ∧
        (∀ i j, (((p i).coeff j).natDegree : ℝ) ≤ C * m) ∧
        (∀ i j k, ‖((p i).coeff j).coeff k‖ ≤ Real.exp (C * N)) ∧
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N],
          ∀ n ≤ m, iteratedDeriv n (fun w => ∑ i,
            (p i).eval₂ (Polynomial.aeval θ).toRingHom ν * w ^ i.1.val *
              L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
                (u₁ / 2 + v) = 0 := by sorry
