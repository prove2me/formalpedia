-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_assemble_auxiliary_grid_jet_matrices
-- name    : WeierstrassEllipticZeta.assemble_auxiliary_grid_jet_matrices
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T16:41:51.50354+00:00
-- url     : https://prove2.me/theorems/0475ebac-4935-438f-948b-5f0150887464
-- title:
--   Assemble uniformly bounded derivative matrices across the enlarged auxiliary grid
-- statement:
--   Let $L$ be a complex period pair, let $\omega,u_1,u_2,\theta,\nu\in\mathbb C$, and let $g\in\mathbb Z[X,Y]$ and $d\in\mathbb Z[X]$. Assume regular auxiliary-grid data, auxiliary-grid parameter data, auxiliary nonlattice coordinate data, bounded nonlattice jet data, and bounded period jet data at $z_0=u_1/2$.
--
--   Regular grid data mean that the map from integer triples to $a_1u_1+a_2u_2+a_3\omega$ is injective, belongs to the lattice precisely when $a_1=a_2=0$, and that two such points are congruent modulo the lattice precisely when their first two coordinates agree. Every point shifted by $u_1/2$ is regular. Grid cardinalities are the product of the side lengths, and their shifted norms have the triangle-inequality radius bound. The data also supply periodicity of $\wp,\wp'$ and quasiperiodicity of $\zeta$ under integral multiples of $\omega$.
--
--   The parameter data supply the stated dimension gap on the shifted smaller grid, together with the already specified auxiliary-parameter positivity, zero-count, radius, and growth inequalities. Translation preserves its cardinality.
--
--   The bounded period data supply, for each $K$, constants $A_p>0$ and a common degree bound $D_p\le A_pm$, before all integers $a$ with $|a|\le3q$. For each such $a$, they provide derivative matrices with $Y$-degree less than $e$, $X$-degree at most $D_p$, length at most $e^{A_pN}$, and dimension envelope $|I|(e+1)(D_p+1)\le e^{A_pN}$. Their entry evaluations are the period case displayed below with $v=a\omega$, and their kernels are exactly the vectors whose associated function vanishes through order $Km$ at $z_0+a\omega$.
--
--   The bounded nonlattice data supply, for each $K,C$, constants $A_n>0$ and a common degree bound $D_n\le A_nm$, before all coordinate polynomials meeting the profiles below. They give the analogous matrix, length, and dimension bounds. At regular points $v,z,z+v$ with compatible coordinates the entry evaluations are the nonlattice case below. If also $z-v$ is regular and the evaluated denominators are nonzero, the kernel is equivalent to vanishing through order $Km$ at $z+v$.
--
--   Then auxiliary grid jet-matrix data hold:
--
--   $$\operatorname{AuxiliaryGridJetMatrixData}(L,\omega,u_1,u_2,\theta,\nu,g,d).$$
--
--   The coordinate hypothesis and complete matrix conclusion are as follows.
--
--   Fix a complex period pair with lattice $\Omega$, and complex numbers $\omega,u_1,u_2,\theta,\nu$. Write $z_0=u_1/2$ and let $\mathscr L(P)$ be the sum of the absolute values of the integer coefficients of a polynomial $P$. For a nonnegative integer $N$, put
--
--   $$s=\lfloor N^{3/16}\rfloor,\qquad q=\lfloor N^{5/8}\log N/64\rfloor,$$
--
--   $$\Gamma_3=\{a_1u_1+a_2u_2+a_3\omega: 0\le a_1,a_2<3s,\ 0\le a_3<3q,\ a_i\in\mathbb Z\}.$$
--
--   For a nonnegative integer $C$, use the coordinate degree and logarithmic length profiles
--
--   $$d_C=(C,Cs^2,Cs^2,Cs^2,C,C,C,C),$$
--
--   $$b_C=(C\log N,C(s^2+\log N),C(s^2+\log N),C(s^2+\log N),C,C,C,C).$$
--
--   A coordinate presentation at $v,z$ consists of eight numerator polynomials $P_a$, denominator polynomials $Q_a$ in $\mathbb Z[X,Y]$, and nonnegative integers $h_a$, such that
--
--   $$\deg P_a,\deg Q_a\le d_{C,a},\qquad
--   \mathscr L(P_a),\mathscr L(Q_a)\le h_a\le e^{b_{C,a}},$$
--
--   $$Q_a(\theta,\nu)\ne0,\qquad P_a(\theta,\nu)=Q_a(\theta,\nu)J_v(z)_a,$$
--
--   $$J_v(z)=(z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z)).$$
--
--   Auxiliary nonlattice coordinate data assert
--
--   $$\exists C\in\mathbb N\ \forall N\text{ sufficiently large}\ \forall v\in\Gamma_3\setminus\Omega,
--   \quad\text{there exists a coordinate presentation at }v,z_0.$$
--
--   The constant and threshold precede all points. Every evaluated denominator is nonzero. The four fixed-coordinate bounds are independent of $N$, the ordinary coordinate has fixed degree and polynomial length in $N$, and the three moving elliptic coordinates have degree $O(s^2)$ and logarithmic length $O(s^2+\log N)$. No derivative matrices or analytic estimates are part of this coordinate property.
--
--   With the coordinate presentations and notation just specified, let $g\in\mathbb Z[X,Y]$, $d\in\mathbb Z[X]$, $e=\deg_Yg$, and $\delta=d(\theta)$. Put
--
--   $$m=\lfloor N/\log N\rfloor,\qquad \ell=\lfloor\sqrt{N\log N}\rfloor,\qquad
--   I=\{0,\ldots,m\}\times\{0,\ldots,\ell\}^2,$$
--
--   $$\Gamma=\{a_1u_1+a_2u_2+a_3\omega:0\le a_1,a_2<s,\ 0\le a_3<q,\ a_i\in\mathbb Z\}.$$
--
--   Auxiliary grid jet-matrix data assert that there is a single nonnegative integer $C$ such that, for each nonnegative integer $K$, there is $A>0$ with the following property for every sufficiently large $N$. There are a nonnegative integer $D$, a polynomial matrix family
--
--   $$R=(R_{v,n,i})_{v\in\Gamma_3,\ 0\le n\le Km,\ i\in I},$$
--
--   and coordinate presentations with the profiles $d_C,b_C$ at every nonlattice point of $\Gamma_3$, satisfying
--
--   $$D\le Am,\qquad |I|(e+1)(D+1)\le e^{AN},\qquad 8(m+1)|\Gamma|\le |I|,$$
--
--   $$\deg_Y R_{v,n,i}<e,\qquad \deg_X([Y^j]R_{v,n,i})\le D\ (j\ge0),\qquad
--   \mathscr L(R_{v,n,i})\le e^{AN}.$$
--
--   Define the ordinary monomials and cleared translates by
--
--   $$f_i(w)=w^{i_0}\wp(w)^{i_2}\zeta(w)^{i_3},\qquad
--   G_{v,i}(w)=(w+v)^{i_0}[2(\wp(v)-\wp(w))]^{3\ell}
--   \wp(w+v)^{i_2}\zeta(w+v)^{i_3}.$$
--
--   Write $Q_{v,a}$ for the denominators in the retained presentation at a nonlattice point, and put
--
--   $$k(n)=(m,5\ell,5\ell,5\ell,J_n,J_n,J_n,J_n),\quad J_n=m+5\ell+n,\qquad
--   \Delta_{v,n}=\prod_{a=0}^7 Q_{v,a}(\theta,\nu)^{k_a(n)}.$$
--
--   The entries retain their exact evaluations in both cases:
--
--   $$R_{v,n,i}(\theta,\nu)=
--   \begin{cases}
--   \delta^{7(m+2\ell+n)}f_i^{(n)}(z_0+v),&v\in\Omega,\\
--   \Delta_{v,n}G_{v,i}^{(n)}(z_0),&v\notin\Omega.
--   \end{cases}$$
--
--   For every point $v\in\Gamma_3$ and every complex coefficient vector $c=(c_i)_{i\in I}$, writing $F_c=\sum_i c_i f_i$, the same matrix family satisfies
--
--   $$\left[\sum_iR_{v,n,i}(\theta,\nu)c_i=0\quad(0\le n\le Km)\right]
--   \Longleftrightarrow
--   \left[F_c^{(n)}(z_0+v)=0\quad(0\le n\le Km)\right].$$
--
--   The matrices and retained presentations precede every coefficient vector. Their degree and length bounds are uniform in the grid point, derivative order, and monomial. Order zero and $K=0$ are included. The dimension gap refers to the smaller grid with $m+1$ equations per point; it does not assert a dimension gap for the whole enlarged derivative family. This interface supplies matrices and their derivative interpretation, while existence and estimates for a nonzero analytic test value remain separate.
-- source:
--   Supporting assembly step for Senthil Kumar K (2026), Section 5 Lemma 8, equations (28)-(29) and the linear system and dimension count in its proof, using Lemma 7(b). The statement retains the enlarged-grid family used in Lemmas 9-10, and includes the period points. Rational-coordinate existence is an explicit hypothesis, and a nonzero test value is not asserted. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices

open scoped Polynomial
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.assemble_auxiliary_grid_jet_matrices
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ) (g : ℤ[X][X]) (d : ℤ[X])
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_coordinates : AuxiliaryNonlatticeCoordinateData L ω u₁ u₂ θ ν)
    (h_nonlattice_bounds : BoundedAuxiliaryNonlatticeJetData L θ ν g)
    (h_period_bounds : BoundedAuxiliaryPeriodJetData L ω (u₁ / 2) θ ν g d) :
    AuxiliaryGridJetMatrixData L ω u₁ u₂ θ ν g d := by sorry
