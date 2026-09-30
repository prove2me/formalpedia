-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_auxiliary_grid_jet_matrices_of_arithmetic_model
-- name    : WeierstrassEllipticZeta.auxiliary_grid_jet_matrices_of_arithmetic_model
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T00:17:57.880797+00:00
-- url     : https://prove2.me/theorems/7f4268ab-79b2-4650-949e-bbe32546adfb
-- title:
--   Bounded grid jet matrices from the arithmetic model
-- statement:
--   Fix a complex period pair $L$, its canonical functions $\wp,\zeta$, and $\omega,u_1,u_2$ with `RegularAuxiliaryGridData`: the integer map $J(a,b,c)=au_1+bu_2+c\omega$ is injective, $J(a,b,c)$ is a period exactly when $a=b=0$, congruence modulo the lattice is determined by the first two coordinates, and every $J(a,b,c)+u_1/2$ is regular. The grid data also include the usual cardinality, radius and period-translation identities.
--
--   Fix an arithmetic model $\theta,\nu\in\mathbb C$, with $\theta$ transcendental over $\mathbb Q$, and a monic $g(X,Y)\in\mathbb Z[X,Y]$ of positive $Y$-degree $e$ such that, for every integer bivariate polynomial $A$,
--   $$A(\theta,\nu)=0\quad\Longleftrightarrow\quad g\mid A.$$
--   Let $d\in\mathbb Z[X]$ and $\delta=d(\theta)\ne0$. Each of the following 18 values must admit a presentation $A_x(\theta,\nu)=\delta x$ with $\deg_Y A_x<e$:
--   $$g_2/4,g_3/4,\omega,\eta(\omega),u_1/2,u_2,\zeta(u_1/2),\wp(u_1/2),\wp'(u_1/2),\wp''(u_1/2),$$
--   $$\wp(u_j),\wp'(u_j),\wp''(u_j),\zeta(u_j)\qquad(j=1,2).$$
--
--
--   Then bounded grid jet-matrix data exist. Put
--   $$m=\lfloor N/\log N\rfloor,\quad \ell=\lfloor\sqrt{N\log N}\rfloor,\quad
--   s=\lfloor N^{3/16}\rfloor,\quad q=\lfloor N^{5/8}\log N/64\rfloor,$$
--   $$I=\{0,\ldots,m\}\times\{0,\ldots,\ell\}^2,\quad
--   \Gamma=\Gamma(s,s,q),\quad\Gamma_3=\Gamma(3s,3s,3q).$$
--   There is a fixed coordinate-presentation constant such that for every integer $K\ge0$ there is $A>0$ for which every sufficiently large $N$ admits an integer $D\le Am$ and polynomial matrices $R(v,n,i)$, indexed by $v\in\Gamma_3$, $0\le n\le Km$, and $i\in I$. They satisfy
--   $$\deg_YR(v,n,i)<e,\quad\deg_XR(v,n,i)\le D,\quad
--   \mathscr L(R(v,n,i))\le e^{AN},$$
--   $$|I|(e+1)(D+1)\le e^{AN},\qquad 8(m+1)|\Gamma|\le |I|.$$
--   Here $\mathscr L$ is the sum of absolute values of integer coefficients. For every complex vector $c=(c_i)$ and every $v\in\Gamma_3$,
--   $$\bigl(\forall n\le Km,\ \sum_i R(v,n,i)(\theta,\nu)c_i=0\bigr)
--   \ \Longleftrightarrow\
--   \bigl(\forall n\le Km,\ F_c^{(n)}(u_1/2+v)=0\bigr),$$
--   where $F_c(w)=\sum_i c_iw^{i_0}\wp(w)^{i_1}\zeta(w)^{i_2}$.
--
--   The matrices retain the full `AuxiliaryGridJetMatrixData` package: at period points their entry evaluations are the ordinary monomial derivatives multiplied by $\delta^{7(m+2\ell+n)}$. At nonperiod points they are derivatives at $u_1/2$ of the translated monomials multiplied by $[2(\wp(v)-\wp(z))]^{3\ell}$, with the eight nonzero evaluated arithmetic denominators raised to weights
--   $$ (m,5\ell,5\ell,5\ell,m+5\ell+n,m+5\ell+n,m+5\ell+n,m+5\ell+n).$$
--   The corresponding eight rational coordinate presentations are for
--   $$ (z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z)) $$
--   at $z=u_1/2$. Their degree profiles are $(C,Cs^2,Cs^2,Cs^2,C,C,C,C)$ and logarithmic-length profiles are $(C\log N,C(s^2+\log N),C(s^2+\log N),C(s^2+\log N),C,C,C,C)$. Each numerator and denominator has the stated degree bound and a common integer coefficient-length bound at most the exponential of the indicated profile. Each evaluated denominator is nonzero and numerator equals denominator times its coordinate.
--
--   All matrices and presentations are chosen before the complex coefficient vector. No derivative-size or bounded-order nonvanishing assumption is needed. This packages the arithmetic constructions of §5, particularly Lemma 7, for the Lemma 8 grid parameters; the eight-denominator presentation is the mission's formal variant.
-- source:
--   Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://doi.org/10.1017/S001309152610145X, §5, Lemmas 7–8 and equation (29); mission Lemma 8 formal-grid variant with factor 1/64.

import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Mathlib.RingTheory.Algebraic.Defs

open scoped Polynomial
open Filter WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.auxiliary_grid_jet_matrices_of_arithmetic_model
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
    AuxiliaryGridJetMatrixData L ω u₁ u₂ θ ν g d := by sorry
