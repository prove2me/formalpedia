-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_auxiliary_period_jet_systems
-- name    : WeierstrassEllipticZeta.bounded_auxiliary_period_jet_systems
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T15:56:09.684305+00:00
-- url     : https://prove2.me/theorems/4dee7e5c-7a45-4cc2-91ca-d3ad5ab665a6
-- title:
--   Uniform degree and exponential coefficient bounds for auxiliary period jets
-- statement:
--   Let $L$ be a complex period pair and let $\omega,u_1,u_2,\theta,\nu\in\mathbb C$. Fix $g\in\mathbb Z[X,Y]$ and $d\in\mathbb Z[X]$. Assume the auxiliary-grid parameter data and the period arithmetic jet-system data at $z=u_1/2$.
--
--   In particular, writing $s=\lfloor N^{3/16}\rfloor$, the parameter data provide, for all sufficiently large $N$,
--
--   $$s\ge2,\qquad \ell s^2\le m,\qquad m\log N\le N.$$
--
--   The period data provide positive integers $B,H$, independent of all cutoffs and period indices. For each integer $a$ and nonnegative $M,L_0,T$, they provide a reduced polynomial matrix with rows $0\le n<T$ and columns $0\le i_0\le L_0$, $0\le i_2,i_3\le M$. With $J_n=L_0+2M+n$, its bounds are
--
--   $$\deg_YR_{n,i}<\deg_Yg,\qquad
--   \deg_X([Y^j]R_{n,i})\le BJ_n,\qquad
--   \mathscr L(R_{n,i})\le n!24^{J_n}(1+|a|)^{L_0+M}H^{J_n+1}.$$
--
--   They also provide the exact derivative evaluations with multiplier $d(\theta)^{7J_n}$ at $u_1/2+a\omega$, and equivalence of the evaluated matrix kernel with vanishing of all derivatives below $T$ of the corresponding auxiliary sum.
--
--   Then the bounded auxiliary period-jet data defined below hold at $z=u_1/2$.
--
--   Fix a complex period pair $L$, complex numbers $\omega,z,\theta,\nu$, and polynomials $g\in\mathbb Z[X,Y]$, $d\in\mathbb Z[X]$. Write $e=\deg_Yg$, $\delta=d(\theta)$, and let $\mathscr L(P)$ be the sum of the absolute values of all integer coefficients of $P$.
--
--   For sufficiently large positive integers $N$, use the auxiliary parameters
--
--   $$m=\lfloor N/\log N\rfloor,\qquad
--   \ell=\lfloor\sqrt{N\log N}\rfloor,\qquad
--   q=\lfloor N^{5/8}\log N/64\rfloor,\qquad
--   I=\{0,\ldots,m\}\times\{0,\ldots,\ell\}^2.$$
--
--   Bounded auxiliary period-jet data mean the following property. For every fixed nonnegative integer $K$, there is a real constant $A>0$ such that, for all sufficiently large $N$, one can choose a nonnegative integer $D$ with
--
--   $$D\le Am,\qquad (m+1)(\ell+1)^2(e+1)(D+1)\le e^{AN}.$$
--
--   This same degree bound works for every integer $a$ satisfying $|a|\le3q$. For each such $a$, there is a matrix
--
--   $$R=(R_{n,i})_{0\le n\le Km,\ i\in I}\quad\text{over }\mathbb Z[X,Y]$$
--
--   such that, for every entry and every nonnegative $j$,
--
--   $$\deg_YR_{n,i}<e,\qquad \deg_X([Y^j]R_{n,i})\le D,\qquad
--   \mathscr L(R_{n,i})\le e^{AN}.$$
--
--   Writing $J_n=m+2\ell+n$, the exact evaluations are
--
--   $$R_{n,i}(\theta,\nu)=\delta^{7J_n}
--   \left.\frac{d^n}{dw^n}\big(w^{i_0}\wp_L(w)^{i_2}\zeta_L(w)^{i_3}\big)
--   \right|_{w=z+a\omega}.$$
--
--   Moreover, for every complex coefficient vector $c=(c_i)_{i\in I}$, set
--
--   $$F_c(w)=\sum_{i\in I}c_iw^{i_0}\wp_L(w)^{i_2}\zeta_L(w)^{i_3}.$$
--
--   The same matrix satisfies
--
--   $$\left[\sum_iR_{n,i}(\theta,\nu)c_i=0\quad(0\le n\le Km)\right]
--   \quad\Longleftrightarrow\quad
--   \left[F_c^{(n)}(z+a\omega)=0\quad(0\le n\le Km)\right].$$
--
--   The constant and threshold precede the period index, the matrix precedes the vector, and $D$ is common to all period indices. The length bound also bounds each individual integer coefficient. Order zero, $K=0$, and both signs of $a$ are included. The padded denominator exponent is inherited from the earlier period-jet construction; it is coarser than the source's exponent in (28). These data do not assert a nonzero derivative or any estimates at nonlattice translates.
-- source:
--   Supporting uniform matrix formulation of Senthil Kumar K (2026), Section 5: the parameters before Lemma 7, equation (28) and the degree/type estimates immediately following it, and their specialization to t <= c*N/log N in the lattice case of Lemma 10. The explicit coefficient-length and dimension bounds and the padded exponent 7*(m+2*l+n) are formalization choices, not a verbatim source theorem. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_PeriodJetBounds

open scoped Polynomial
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.bounded_auxiliary_period_jet_systems
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ) (g : ℤ[X][X]) (d : ℤ[X])
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_period_jets : PeriodArithmeticJetSystemData L ω (u₁ / 2) θ ν g d) :
    BoundedAuxiliaryPeriodJetData L ω (u₁ / 2) θ ν g d := by sorry
