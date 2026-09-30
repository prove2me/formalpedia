-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_sigma_inverse_bounds
-- name    : WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_sigma_inverse_bounds
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T23:00:49.051471+00:00
-- url     : https://prove2.me/theorems/315a88cc-b9cb-4dab-967c-7faf7c744bce
-- title:
--   Analytic extraction with sigma regularizer inverse bounds supplied
-- statement:
--   Let $L$ be a complex period pair, and let $\omega,u_1,u_2\in\mathbb C$ have regular auxiliary-grid data. Thus integer grid points are distinct, their lattice congruences are determined by their first two coordinates, and every point shifted by $u_1/2$ is outside the lattice. The finite grids have cardinality $A_1A_2A_3$ and shifted radius at most
--
--   $$
--   A_1|u_1|+A_2|u_2|+A_3|\omega|+|u_1|/2.
--   $$
--
--   The data also include the elliptic periodicity formulas and
--
--   $$
--   \zeta(z+n\omega)=\zeta(z)+n\eta(\omega)
--   \qquad(n\in\mathbb Z,\ z\notin\Omega).
--   $$
--
--   Assume the canonical zeta derivative identity and the multiplied elliptic and zeta addition identities at regular arguments. Let $\theta$ be transcendental over $\mathbb Q$, let $\nu\in\mathbb C$, and let $g\in\mathbb Z[X,Y]$ be monic of positive $Y$-degree $r$ with
--
--   $$
--   p(\theta,\nu)=0\iff g\mid p.
--   $$
--
--   For a fixed $d\in\mathbb Z[X]$ with $d(\theta)\ne0$, assume the eighteen auxiliary values admit presentations of $Y$-degree less than $r$ after multiplication by $d(\theta)$. Those values are
--
--   $$
--   g_2/4,g_3/4,\omega,\eta(\omega),u_1/2,u_2,
--   \zeta(u_1/2),\wp(u_1/2),\wp'(u_1/2),\wp''(u_1/2),
--   $$
--
--   $$
--   \wp(u_j),\wp'(u_j),\wp''(u_j),\zeta(u_j)\quad(j=1,2).
--   $$
--
--   Assume reduced arithmetic jet-system data as follows.
--
--   Fix a period pair $L$, complex numbers $\theta,\nu$, and $g\in\mathbb Z[X][Y]$. For a polynomial, $\ell$ denotes the sum of the absolute values of all integer coefficients.
--
--   Reduced arithmetic jet-system data mean that there exist positive integers $B,H$ with the following property. For any nonnegative $M,L_0,T$, let
--
--   $$
--   I=\{0,\ldots,L_0\}\times\{0,\ldots,M\}^2,\qquad
--   k(n)=(L_0,5M,5M,5M,K_n,K_n,K_n,K_n),\quad K_n=L_0+5M+n.
--   $$
--
--   Choose eight numerator and denominator polynomials $S_a,Q_a\in\mathbb Z[X,Y]$, whose total degrees are at most $d_a$ and lengths at most $h_a$, respectively. There exists a matrix
--
--   $$
--   R=(R_{n,i})_{\substack{0\le n<T\\i\in I}}
--   $$
--
--   of integer bivariate polynomials. Writing $D_n=\sum_{a=0}^7 k_a(n)d_a$, every entry satisfies
--
--   $$
--   \deg_Y R_{n,i}<\deg_Yg,\qquad
--   \deg_X[Y^j]R_{n,i}\le BD_n\quad(j\ge0),
--   $$
--
--   $$
--   \ell(R_{n,i})\le
--   n!\,2^{41(L_0+M+n)}\left(\prod_{a=0}^7h_a^{k_a(n)}\right)H^{D_n+1}.
--   $$
--
--   This matrix precedes the following points and coefficient vectors. For any $v,z,z+v$ outside the lattice, suppose the coordinate presentations satisfy
--
--   $$
--   S_a(\theta,\nu)=Q_a(\theta,\nu)J_v(z)_a,
--   $$
--
--   where
--
--   $$
--   J_v(z)=(z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z)).
--   $$
--
--   For $i=(i_0,i_2,i_3)$, set
--
--   $$
--   G_i(w)=(w+v)^{i_0}[2(\wp(v)-\wp(w))]^{3M}
--          \wp(w+v)^{i_2}\zeta(w+v)^{i_3},\qquad
--   \Delta_n=\prod_{a=0}^7Q_a(\theta,\nu)^{k_a(n)}.
--   $$
--
--   The exact entry evaluations are
--
--   $$
--   R_{n,i}(\theta,\nu)=\Delta_nG_i^{(n)}(z).
--   $$
--
--   If additionally $z-v$ is regular and all eight evaluated denominators are nonzero, then for every complex vector $c=(c_i)_{i\in I}$,
--
--   $$
--   \left(\forall\,0\le n<T,\ \sum_iR_{n,i}(\theta,\nu)c_i=0\right)
--   \ \Longleftrightarrow\
--   \left(\forall\,0\le n<T,\ F_c^{(n)}(z+v)=0\right),
--   $$
--
--   where
--
--   $$
--   F_c(w)=\sum_{i\in I}c_iw^{i_0}\wp(w)^{i_2}\zeta(w)^{i_3}.
--   $$
--
--   The exact evaluation identities also hold with zero coordinate denominators; nonzero denominators are required only for kernel equivalence. Constants are uniform in all cutoffs, orders, and presentations. The property assembles bounded reduced derivative presentations into finite linear equations. It does not produce grid-coordinate presentations, prove that their denominators are nonzero, choose asymptotic parameters, or establish a small nonzero test value.
--
--   Also assume auxiliary-grid interpolation data as follows.
--
--   Fix complex numbers $\omega,u_1,u_2$. For a triple of nonnegative integers $A=(A_1,A_2,A_3)$, let
--
--   $$
--   S_A=\{a_1u_1+a_2u_2+a_3\omega+u_1/2:
--              0\le a_i<A_i,\ a_i\in\mathbb Z\},
--   $$
--
--   $$
--   q_A=A_1|u_1|+A_2|u_2|+A_3|\omega|+|u_1|/2.
--   $$
--
--   Auxiliary-grid interpolation data mean the following property. Choose a nonnegative integer $T$, functions $f,G,\psi:\mathbb C\to\mathbb C$, with $G$ entire and $f,\psi$ analytic at every point of $S_A$. Suppose $G=\psi f$ in a neighborhood of each grid point and
--
--   $$
--   f^{(j)}(x)=0\qquad(x\in S_A,\ 0\le j<T).
--   $$
--
--   For all $0<r<R$ and $C\in\mathbb R$ with $q_A\le r$ and $|G(z)|\le C$ on $|z|=R$, put $N_A=TA_1A_2A_3$. Then
--
--   $$
--   |G(z)|\le C\left(\frac{2r}{R}\right)^{N_A}\qquad(|z|\le r),
--   $$
--
--   and, whenever $\rho>0$ and $|w|+\rho\le r$,
--
--   $$
--   |G^{(n)}(w)|\le\frac{n!}{\rho^n}\,C
--                      \left(\frac{2r}{R}\right)^{N_A}\qquad(n\ge0).
--   $$
--
--   The multiplier need not be nonzero. Empty grids and $T=0$ are included. This predicate records the effect of analytic regularization and interpolation once the regularized entire function and its outer-circle bound have been provided. It does not assert existence or growth estimates for a Weierstrass sigma regularizer.
--
--   Also assume the following elliptic regularization data.
--
--   Fix a period pair $L$ and complex numbers $\omega,u_1,u_2$. Write
--
--   $$\Phi_0=\zeta_L,\qquad\Phi_1=\wp_L,\qquad\Phi_2=\wp'_L.$$
--
--   Elliptic regularization data mean the following property. Supply entire functions $\sigma,S_0,S_1,S_2$ satisfying
--
--   $$S_j(z)=\sigma(z)^{j+1}\Phi_j(z)\qquad(z\notin L,\ 0\le j\le2).$$
--
--   For any finite index set $I$, complex shift $v$, complex coefficients $c_i$, and nonnegative integers $\ell_i,e_{ij},D,K$ with
--
--   $$\ell_i\le D,\qquad e_{i0}+2e_{i1}+3e_{i2}\le K,$$
--
--   put
--
--   $$f(z)=\sum_i c_i(z+v)^{\ell_i}\prod_{j=0}^2\Phi_j(z)^{e_{ij}}.$$
--
--   There is an entire function $G$, chosen independently of the radius, grid, and bounds, with $G=\sigma^Kf$ outside the lattice. If $B\ge1$ bounds the absolute values of $\sigma,S_0,S_1,S_2$ throughout $|z|\le R$, define
--
--   $$C_R=\left(\sum_i|c_i|\right)\max(1,R+|v|)^D B^K.$$
--
--   Then $|G(z)|\le C_R$ on $|z|\le R$. Moreover, choose nonnegative integers $A_1,A_2,A_3,T$ and radii $0<r<R$ such that
--
--   $$A_1|u_1|+A_2|u_2|+A_3|\omega|+|u_1|/2\le r.$$
--
--   Suppose all derivatives of $f$ below order $T$ vanish on
--
--   $$\{a_1u_1+a_2u_2+a_3\omega+u_1/2:0\le a_i<A_i\}.$$
--
--   Then, with $Q=TA_1A_2A_3$,
--
--   $$|G(z)|\le C_R(2r/R)^Q\qquad(|z|\le r),$$
--
--   $$|G^{(n)}(z)|\le \frac{n!}{\rho^n}C_R(2r/R)^Q
--   \qquad(\rho>0,\ |z|+\rho\le r,\ n\ge0).$$
--
--   The definition supplies the analytic extension and its interpolation consequences conditional on the four entire factors and their bounds. It does not assert existence of those factors or an order-two growth bound for them. At lattice points the entire extension need not equal the product formed from totalized meromorphic values.
--
--   Also assume cleared-addition entire data, as follows.
--
--   Let $L$ be a complex period pair, with lattice $\Omega$ and canonical functions $\zeta,\wp,\wp'$. Assume their multiplied addition identities at regular arguments. Supply entire functions $\sigma,S_0,S_1,S_2$ satisfying
--
--   $$S_0=\sigma\zeta,\qquad S_1=\sigma^2\wp,\qquad S_2=\sigma^3\wp'
--   \qquad\text{outside }\Omega.$$
--
--   Let $I$ be any finite index set, let $v\notin\Omega$, and choose complex coefficients $c_i$ and nonnegative integers $\ell_{0i},\ell_{2i},\ell_{3i},D,M$ with
--
--   $$\ell_{0i}\le D,\qquad\ell_{2i},\ell_{3i}\le M.$$
--
--   Define the translated, cleared auxiliary sum
--
--   $$f(z)=\sum_{i\in I}c_i(z+v)^{\ell_{0i}}
--   [2(\wp(v)-\wp(z))]^{3M}\wp(z+v)^{\ell_{2i}}\zeta(z+v)^{\ell_{3i}}.$$
--
--   There exists a single entire function $G$, chosen before any radius or bounds, with
--
--   $$G(z)=\sigma(z)^{15M}f(z)\qquad(z,z+v\notin\Omega).$$
--
--   Put
--
--   $$V_v=1+|\zeta(v)|+|\wp(v)|+|\wp'(v)|,\qquad K_v=36V_v^3.$$
--
--   For every $R\in\mathbb R$ and $B\ge1$, if all four basic entire functions are bounded in absolute value by $B$ on $|z|\le R$, then
--
--   $$|G(z)|\le C_R:=\left(\sum_i|c_i|\right)
--   \max(1,R+|v|)^D K_v^{15M}B^{90M}\qquad(|z|\le R).$$
--
--   The finite set may be empty, coefficients may vanish, and $D=M=0$ is allowed. Neither $\sigma$ nor the addition factor is assumed nonzero. The identity is restricted to regular arguments; the entire extension supplies its own values at poles. This is a conditional version of the construction in Lemma 6(ii), with a coarse explicit growth constant. It does not construct the basic sigma factors or assert the source's sharper displayed numerical bound.
--
--   For fixed $L,\omega,u_1,u_2$, cleared-addition entire data assert the preceding entire-extension and disk-bound property for every choice of the four basic factors, regular shift, finite coefficients, and exponents. The data also assert the following interpolation consequences for the same entire function $G$.
--
--   Let $A=(A_1,A_2,A_3)$ and $T$ be nonnegative integers. Suppose $0<r<R$, $B\ge1$, the four factors are bounded by $B$ on the closed radius-$R$ disk, and
--
--   $$A_1|u_1|+A_2|u_2|+A_3|\omega|+|u_1|/2\le r.$$
--
--   Write
--
--   $$\Gamma_A=\{a_1u_1+a_2u_2+a_3\omega+u_1/2:0\le a_i<A_i\}.$$
--
--   Assume $x+v\notin\Omega$ for every $x\in\Gamma_A$, and
--
--   $$f^{(t)}(x)=0\qquad(x\in\Gamma_A,\ 0\le t<T).$$
--
--   Then
--
--   $$|G(z)|\le C_R(2r/R)^{TA_1A_2A_3}\qquad(|z|\le r),$$
--
--   $$|G^{(n)}(z)|\le \frac{n!}{\rho^n}C_R(2r/R)^{TA_1A_2A_3}
--   \qquad(\rho>0,\ |z|+\rho\le r,\ n\ge0).$$
--
--   The entire function precedes all choices of grids, radii and bounds. The data do not provide the four basic factors, establish their nonvanishing or growth, or prove that a test value is nonzero.
--
--   Also assume the following period arithmetic jet-system data at $z=u_1/2$.
--
--   For fixed $L,\omega,z,\theta,\nu$, a monic relation $g\in\mathbb Z[X,Y]$, and $d\in\mathbb Z[X]$, the period arithmetic jet-system data assert the following uniform property. Write $\delta=d(\theta)$ and $e=\deg_Yg$. There exist positive integers $B,H$ such that for every integer $a$ and nonnegative integers $M,L_0,T$, with
--
--   $$I=\{0,\ldots,L_0\}\times\{0,\ldots,M\}^2,\qquad K_n=L_0+2M+n,$$
--
--   there is a matrix $R=(R_{n,i})_{0\le n<T,\,i\in I}$ over $\mathbb Z[X,Y]$ satisfying
--
--   $$\deg_YR_{n,i}<e,\qquad
--   \deg_X([Y^j]R_{n,i})\le BK_n\quad(j\ge0),$$
--
--   $$\mathscr L(R_{n,i})\le n!\,24^{K_n}(1+|a|)^{L_0+M}H^{K_n+1},$$
--
--   $$R_{n,i}(\theta,\nu)=\delta^{7K_n}
--   \left.\frac{d^n}{dw^n}\big(w^{i_0}\wp(w)^{i_2}\zeta(w)^{i_3}\big)
--   \right|_{w=z+a\omega}.$$
--
--   The same matrix, chosen before all coefficient vectors, satisfies for every $c\in\mathbb C^I$
--
--   $$\left[\sum_iR_{n,i}(\theta,\nu)c_i=0\ \ (0\le n<T)\right]
--   \iff
--   \left[\left.\frac{d^n}{dw^n}\sum_i c_iw^{i_0}\wp(w)^{i_2}\zeta(w)^{i_3}
--   \right|_{w=z+a\omega}=0\ \ (0\le n<T)\right].$$
--
--   The denominator exponent $7K_n$ is a uniform padding from coordinatewise clearing. It is explicitly coarser than the exponent in source equation (28); the degree and logarithmic height still have the required linear dependence on the degree and derivative parameters. The data concern only shifts by integer multiples of $\omega$. They neither supply coordinates at other grid points nor prove the zero estimate.
--
--
--   Also assume the following rounded-parameter and actual-grid estimates.
--
--   For a nonnegative integer $N$, define
--
--   $$m=\lfloor N/\log N\rfloor,\qquad
--   \ell=\lfloor\sqrt{N\log N}\rfloor,\qquad
--   s=\lfloor N^{3/16}\rfloor,\qquad
--   q=\lfloor N^{5/8}\log N/64\rfloor,\qquad
--   R=N^{49/72}.$$
--
--   Only sufficiently large $N$ enter the estimates. The formal definitions use nonnegative integer floors, which agree with the displayed floors there. The constant $1/64$ is one explicit small choice for the source's freely chosen grid constant.
--
--   Write $\Omega$ for the period lattice and put
--
--   $$U=|u_1|+|u_2|+|\omega|+1,\qquad r=4qU,$$
--
--   $$\Gamma_N=\{a_1u_1+a_2u_2+a_3\omega+u_1/2:
--   0\le a_1,a_2<s,\ 0\le a_3<q,\ a_i\in\mathbb Z\},$$
--
--   $$\Gamma_N^{(3)}=\{a_1u_1+a_2u_2+a_3\omega+u_1/2:
--   0\le a_1,a_2<3s,\ 0\le a_3<3q,\ a_i\in\mathbb Z\}.$$
--
--   The grid parameter data assert that, for every fixed $B>0$, all sufficiently large $N$ satisfy
--
--   $$m,\ell,q\ge1,\qquad 2\le s\le q,$$
--
--   $$8(m+1)|\Gamma_N|\le(m+1)(\ell+1)^2,\qquad
--   \frac{N^2}{512}\le(m+1)|\Gamma_N|\le\frac{N^2}{32},$$
--
--   $$m\log N\le N,\qquad \ell s^2\le m,\qquad R\ge1,\qquad r>0,$$
--
--   $$z\in\Gamma_N^{(3)}\ \Longrightarrow\ z\notin\Omega\ \text{and}\ |z|+1\le r,$$
--
--   $$\frac{2r}{R}\le N^{-1/36},\qquad B\ell R^2\le N^2.$$
--
--   Here the grids are the actual finite sets, so their cardinalities count distinct points. All shifted points are regular, including shifts whose unshifted point lies in the lattice. The counts allow vanishing conditions on the entire shifted grid; the data do not assert that an auxiliary function satisfying those conditions has already been constructed. Basic sigma factors, arithmetic coordinate presentations, coefficient envelopes, and the zero estimate are separate obligations.
--
--
--   Also assume the following uniform decay data on translated grids.
--
--   For fixed complex $\omega,u_1,u_2$, put
--
--   $$m=\lfloor N/\log N\rfloor,\quad s=\lfloor N^{3/16}\rfloor,\quad
--   q=\lfloor N^{5/8}\log N/64\rfloor,\quad R=N^{49/72},$$
--
--   $$r=4q(|u_1|+|u_2|+|\omega|+1),\qquad
--   \Gamma_N=\{a_1u_1+a_2u_2+a_3\omega+u_1/2:
--   0\le a_1,a_2<s,\ 0\le a_3<q,\ a_i\in\mathbb Z\}.$$
--
--   The decay data assert the following proposition for every fixed $B\ge0$ and $K>0$, for all sufficiently large integers $N$, uniformly in all subsequent choices.
--
--   Let $|v|\le r$ and write $\Delta=\Gamma_N-v$. Supply functions $f,G,\psi$ such that $G$ is entire, while $f,\psi$ are analytic near every point of $\Delta$ and satisfy $G=\psi f$ locally there. Assume
--
--   $$f^{(j)}(x)=0\quad(x\in\Delta,\ 0\le j<m+1),\qquad
--   \max_{|z|=R}|G(z)|\le e^{BN^2}.$$
--
--   For every complex $w$ and nonnegative integer $n$ with
--
--   $$|w|+1\le 2r,\qquad n\le Km,$$
--
--   the regularized derivative satisfies
--
--   $$|G^{(n)}(w)|\le \exp\!\left(-\frac{N^2\log N}{73728}\right).$$
--
--   If $f,\psi$ are also analytic near $w$, with $G=\psi f$ there, and
--
--   $$f^{(j)}(w)=0\quad(0\le j<n),\qquad \psi(w)\ne0,\qquad
--   |\psi(w)|^{-1}\le e^{BN^2},$$
--
--   then
--
--   $$|f^{(n)}(w)|\le \exp\!\left(-\frac{N^2\log N}{73728}\right).$$
--
--   The double inner radius accommodates arbitrary translates with $|v|\le r$. The constant $1/73728$ is a coarse explicit choice, not a quoted constant from the source. This predicate supplies the interpolation implication; construction and growth of the basic sigma factors, the inverse multiplier bound, and a nonzero test derivative remain separate obligations. No regularity or nonvanishing is inferred from totalized meromorphic values.
--
--
--   Also assume the following bounded period-jet data at $z=u_1/2$.
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
--
--
--   Also assume the following conditional nonlattice matrix bounds.
--
--   Fix a complex period pair $L$, complex numbers $\theta,\nu$, and $g\in\mathbb Z[X,Y]$. Write $e=\deg_Yg$ and let $\mathscr L(P)$ denote the sum of the absolute values of all integer coefficients of $P$.
--
--   For all sufficiently large positive integers $N$, put
--
--   $$m=\lfloor N/\log N\rfloor,\qquad
--   \ell=\lfloor\sqrt{N\log N}\rfloor,\qquad s=\lfloor N^{3/16}\rfloor,\qquad
--   I=\{0,\ldots,m\}\times\{0,\ldots,\ell\}^2.$$
--
--   For nonnegative integers $K,C$, define the eight coordinate degree and logarithmic length bounds
--
--   $$d=(C,Cs^2,Cs^2,Cs^2,C,C,C,C),$$
--
--   $$b=(C\log N,C(s^2+\log N),C(s^2+\log N),C(s^2+\log N),C,C,C,C).$$
--
--   The derivative weights are
--
--   $$k(n)=(m,5\ell,5\ell,5\ell,J_n,J_n,J_n,J_n),\qquad J_n=m+5\ell+n.$$
--
--   Bounded auxiliary nonlattice jet data assert that, for every $K,C$, there is $A>0$ such that, for all sufficiently large $N$, one can choose a nonnegative integer $D$ satisfying
--
--   $$D\le Am,\qquad (m+1)(\ell+1)^2(e+1)(D+1)\le e^{AN}.$$
--
--   This degree bound is chosen before the following coordinate presentations. Choose eight numerator and denominator polynomials $P_a,Q_a\in\mathbb Z[X,Y]$ and nonnegative integer length bounds $h_a$ such that
--
--   $$\deg P_a,\deg Q_a\le d_a,\qquad
--   \mathscr L(P_a),\mathscr L(Q_a)\le h_a\le e^{b_a}\qquad(0\le a<8).$$
--
--   There is a polynomial matrix
--
--   $$R=(R_{n,i})_{0\le n\le Km,\ i\in I}$$
--
--   with
--
--   $$\deg_Y R_{n,i}<e,\qquad
--   \deg_X([Y^j]R_{n,i})\le D\quad(j\ge0),\qquad
--   \mathscr L(R_{n,i})\le e^{AN}.$$
--
--   The matrix is chosen before any complex evaluation points $v,z$. Suppose $v,z,z+v$ lie outside the period lattice and
--
--   $$P_a(\theta,\nu)=Q_a(\theta,\nu)\mathcal J_v(z)_a,$$
--
--   $$\mathcal J_v(z)=(z+v,\zeta_L(v),\wp_L(v),\wp'_L(v),
--   \zeta_L(z),\wp_L(z),\wp'_L(z),\wp''_L(z)).$$
--
--   Put
--
--   $$G_i(w)=(w+v)^{i_0}[2(\wp_L(v)-\wp_L(w))]^{3\ell}
--   \wp_L(w+v)^{i_2}\zeta_L(w+v)^{i_3},\qquad
--   \Delta_n=\prod_{a=0}^7Q_a(\theta,\nu)^{k_a(n)}.$$
--
--   Then the exact entry evaluations are
--
--   $$R_{n,i}(\theta,\nu)=\Delta_nG_i^{(n)}(z).$$
--
--   If in addition $z-v$ lies outside the lattice and every $Q_a(\theta,\nu)$ is nonzero, then, for every complex vector $c=(c_i)_{i\in I}$, writing
--
--   $$F_c(w)=\sum_{i\in I}c_iw^{i_0}\wp_L(w)^{i_2}\zeta_L(w)^{i_3},$$
--
--   the same matrix satisfies
--
--   $$\left[\sum_i R_{n,i}(\theta,\nu)c_i=0\quad(0\le n\le Km)\right]
--   \quad\Longleftrightarrow\quad
--   \left[F_c^{(n)}(z+v)=0\quad(0\le n\le Km)\right].$$
--
--   The constant and threshold precede all coordinate polynomials; $D$ is common to every presentation and derivative order. The matrix precedes the points and vectors. Both $K=0$ and $C=0$ are allowed. Zero denominators are permitted for the exact evaluation identity, and nonzero evaluated denominators are explicit hypotheses of the kernel equivalence. This is a conditional bound for nonlattice derivative matrices: existence of coordinate presentations satisfying the profiles, their denominator nonvanishing, and a nonzero test derivative are separate obligations.
--
--
--   Also assume assembled grid jet-matrix data, including the retained coordinate presentations, as follows.
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
--
--   In addition, suppose a normalized entire sigma differential solution $\sigma$ and three entire functions $S_0,S_1,S_2$ are supplied, with
--
--   $$\sigma(0)=0,\quad\sigma'(0)=1,\quad
--   \sigma'(z)=\zeta(z)\sigma(z)\quad(z\notin\Omega),$$
--
--   $$S_0=\sigma\zeta,\quad S_1=\sigma^2\wp,\quad S_2=\sigma^3\wp'
--   \quad\text{outside }\Omega.$$
--
--   Suppose a single real constant $A>0$ bounds these four entire functions globally:
--
--   $$|\sigma(z)|\le e^{A(1+|z|^2)},\qquad
--   |S_j(z)|\le e^{A(1+|z|^2)}
--   \quad(z\in\mathbb C,\ j=0,1,2).$$
--
--   Assume also that $\sigma(z)\ne0$ outside $\Omega$. For all sufficiently large integers $N$, suppose that the two sigma regularizers obey
--
--   $$
--   |\sigma(u_1/2)^{15\ell}|^{-1}\le e^{N^2},
--   $$
--
--   $$
--   |\sigma(u_1/2+v)^{3\ell}|^{-1}\le e^{N^2}
--   \quad\bigl(v\in\Gamma(3S,3S,3S_3)\cap\Omega\bigr).
--   $$
--
--   Here $\ell=\lfloor\sqrt{N\log N}\rfloor$ is the auxiliary degree, $S=\lfloor N^{3/16}\rfloor$, and $S_3=\lfloor N^{5/8}\log N/64\rfloor$, as in the supplied grid data.
--
--   Then there exist $a,c>0$ such that every sufficiently large $N$ admits a complex auxiliary system with
--
--   $$
--   b=(3+|\theta|+|\nu|)a,\qquad E<\deg_Y g.
--   $$
--
--   The system has the degree, height, size, and dimension-gap bounds in `ComplexAuxiliarySystem`. Every nonzero vector in its evaluated equation kernel with coordinate magnitudes at most $e^{bN}$ has a nonzero test value of magnitude at most $e^{-cN^2\log N}$. The matrices and finite test family precede the choice of vector.
--
--   The entire sigma factors, their finite quadratic exponential growth, and the two reciprocal-power estimates are inputs to this continuation. The remaining work includes the zero estimate producing a bounded-order nonzero derivative, the cleared nonlattice arithmetic estimates, and assembling a finite test family with the required decay. Every original geometric, arithmetic, matrix, regularization, and growth hypothesis and the exact complex-auxiliary-system conclusion are retained.
-- source:
--   Senthil Kumar K (2026), Section 5, Lemmas 8–10, equation (35), and the period case concluding Lemma 10, https://doi.org/10.1017/S001309152610145X. This continuation receives the actual two sigma inverse estimates in addition to the existing entire-factor and growth hypotheses; zero estimates and finite-test extraction remain obligations.

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Definitions.Def_WeierstrassEllipticZeta_NonlatticeJetBounds
import Definitions.Def_WeierstrassEllipticZeta_PeriodJetBounds
import Definitions.Def_WeierstrassEllipticZeta_InterpolationDecay
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryParameters
import Definitions.Def_WeierstrassEllipticZeta_ReducedJetSystems
import Definitions.Def_WeierstrassEllipticZeta_GridInterpolation
import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
import Definitions.Def_WeierstrassEllipticZeta_ClearedEntire
import Definitions.Def_WeierstrassEllipticZeta_PeriodJets
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Polynomial
open Filter

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_sigma_inverse_bounds
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_decay : AuxiliaryGridDecayData ω u₁ u₂)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (h_wp_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (ν : ℂ)
    (g : ℤ[X][X]) (hg_monic : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_kernel : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
    (h_jet_systems : ReducedArithmeticJetSystemData L θ ν g)
    (h_nonlattice_bounds : BoundedAuxiliaryNonlatticeJetData L θ ν g)
    (h_interpolation : AuxiliaryGridInterpolationData ω u₁ u₂)
    (h_regularization : EllipticRegularizationData L ω u₁ u₂)
    (h_cleared_entire : ClearedAdditionEntireData L ω u₁ u₂)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_period_jets : PeriodArithmeticJetSystemData L ω (u₁ / 2) θ ν g d)
    (h_period_bounds : BoundedAuxiliaryPeriodJetData L ω (u₁ / 2) θ ν g d)
    (h_grid_matrices : AuxiliaryGridJetMatrixData L ω u₁ u₂ θ ν g d)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.natDegree < g.natDegree ∧
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i))
    (D : EllipticSigmaDifferentialData L) (S : Fin 3 → ℂ → ℂ)
    (h_factors_entire : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (h_factors_eq : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
      S j z = D.sigma z ^ (j.val + 1) * ellipticPoleCoordinates L z j)
    (A : ℝ) (hA : 0 < A)
    (h_sigma_growth : ∀ z : ℂ, ‖D.sigma z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (h_factor_growth : ∀ (z : ℂ) (j : Fin 3),
      ‖S j z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (h_sigma_nonzero : ∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0)
    (h_sigma_inverse : ∀ᶠ N : ℕ in Filter.atTop,
      ‖D.sigma (u₁ / 2) ^ (15 * auxiliaryL N)‖⁻¹ ≤ Real.exp ((N : ℝ) ^ 2) ∧
      ∀ v ∈ auxiliaryGrid u₁ u₂ ω
          ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
        v ∈ L.lattice →
          ‖D.sigma (u₁ / 2 + v) ^ (3 * auxiliaryL N)‖⁻¹ ≤
            Real.exp ((N : ℝ) ^ 2)) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by sorry
