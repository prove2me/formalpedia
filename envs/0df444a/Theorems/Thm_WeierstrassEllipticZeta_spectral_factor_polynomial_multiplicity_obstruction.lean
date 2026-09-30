-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_spectral_factor_polynomial_multiplicity_obstruction
-- name    : WeierstrassEllipticZeta.spectral_factor_polynomial_multiplicity_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-10T23:34:53.520376+00:00
-- url     : https://prove2.me/theorems/f8b27e52-60e0-4b3d-b780-deeb9f575257
-- title:
--   Multiplicity obstruction with polynomial calculus in spectral factors
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$, invariants $g_2,g_3$, normalized entire sigma differential data $\sigma$, and entire functions $S_0,\ldots,S_4$ without a common zero, satisfying
--
--   $$S(z)=\sigma(z)^3(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2)\quad(z\notin\Lambda).$$
--
--   Let $\eta:\Lambda\to\mathbb C$ be a $\mathbb Z$-linear map equal to the canonical quasiperiods. Put
--
--   $$E_\eta=\mathbb C^2/\{(\omega,-\eta(\omega)):\omega\in\Lambda\},\qquad
--   G_\eta=\mathbb C\times E_\eta,\qquad \varphi(z)=(z,[(z,0)]).$$
--
--   Let $Z_{g_2,g_3}\subseteq\mathbb P^4(\mathbb C)$ be the locus
--
--   $$X_0X_4-X_2X_3-2X_1^2=0,\qquad
--   X_0X_2^2-4X_1^3+g_2X_0^2X_1+g_3X_0^3=0.$$
--
--   Let
--
--   $$Z^\circ_{g_2,g_3}=\{[X]\in Z_{g_2,g_3}:X_0\ne0\ \text{or}\ X_2\ne0\}.$$
--
--   Suppose a bijection $P:E_\eta\simeq Z^\circ_{g_2,g_3}$ has nonzero homogeneous coordinate vectors
--
--   $$P([(z,u)])=[S_0(z):S_1(z):S_2(z):S_3(z)+uS_0(z):S_4(z)+uS_2(z)]$$
--
--   for all $z,u\in\mathbb C$. Assume also that $Z^\circ_{g_2,g_3}$ is equipped with a projective additive-fiber model $(\pi,A)$: the projection $\pi([X])=[X_0:X_1:X_2]$ has exactly the Weierstrass cubic as image, the action is
--
--   $$A(u,[X])=[X_0:X_1:X_2:X_3+uX_0:X_4+uX_2],$$
--
--   it obeys the additive action laws, and $\pi(p)=\pi(q)$ if and only if there is a unique $u$ with $A(u,p)=q$. Suppose $P$ respects the additive inclusion $i(u)=[(0,u)]$:
--
--   $$P(e+i(u))=A(u,P(e)).$$
--
--   Write $r(z)$ for a chosen nonzero representative of the underlying projective point $P([(z,0)])$.
--
--   Assume in addition the following polynomial differential equations for the normalized coordinate functions.
--
--   On the open set where $S_0\ne0$, put
--
--   $$x=\frac{S_1}{S_0},\qquad y=\frac{S_2}{S_0},\qquad t=\frac{S_3}{S_0}.$$
--
--   Then these functions have complex derivatives
--
--   $$x'=y,\qquad y'=6x^2-\frac{g_2}{2},\qquad t'=-x.$$
--
--   On the open set where $S_2\ne0$, put
--
--   $$a=\frac{S_0}{S_2},\qquad b=\frac{S_1}{S_2},\qquad d=\frac{S_4}{S_2}.$$
--
--   Their complex derivatives are
--
--   $$\begin{aligned}
--   a'&=-6b^2+\frac{g_2}{2}a^2,\\
--   b'&=-\frac12-g_2ab-\frac{3g_3}{2}a^2,\\
--   d'&=-2g_2b^2-3g_3ab.
--   \end{aligned}$$
--
--   Each assertion holds at every point where its specified denominator is nonzero, without excluding lattice points.
--
--   Assume also the following algebraic description of the chart jets.
--
--   For complex parameters $g_2,g_3$, consider the two polynomial derivations on four-variable polynomial rings over $\mathbb C$:
--
--   $$\mathcal D_0=\partial_t+y\partial_x+(6x^2-g_2/2)\partial_y-x\partial_r$$
--
--   in variables $(t,x,y,r)$, and
--
--   $$\mathcal D_2=\partial_t+(-6b^2+g_2a^2/2)\partial_a
--   +(-1/2-g_2ab-3g_3a^2/2)\partial_b
--   +(-2g_2b^2-3g_3ab)\partial_d$$
--
--   in variables $(t,a,b,d)$. Their respective cubic polynomials are
--
--   $$G_0=y^2-4x^3+g_2x+g_3,\qquad G_2=a-4b^3+g_2a^2b+g_3a^3.$$
--
--   Given five functions $S_j:\mathbb C\to\mathbb C$, the coordinate maps are
--
--   $$f_0(z)=(z,S_1/S_0,S_2/S_0,S_3/S_0)(z),\qquad
--   f_2(z)=(z,S_0/S_2,S_1/S_2,S_4/S_2)(z),$$
--
--   used on $U_0=\{S_0\ne0\}$ and $U_2=\{S_2\ne0\}$, respectively. These are the affine coordinates for the zero and second homogeneous-coordinate charts of the elliptic-extension model.
--
--   For $c\in\{0,2\}$, the derivation annihilates its cubic:
--
--   $$\mathcal D_cG_c=0.$$
--
--   For every polynomial $p$ in the four coordinates and every integer $n\ge0$,
--
--   $$\deg(\mathcal D_c^n p)\le\deg(p)+n.$$
--
--   At each $z\in U_c$, the exact derivative identity is
--
--   $$\frac{d^n}{dz^n}\big(p(f_c(z))\big)=(\mathcal D_c^n p)(f_c(z)),$$
--
--   and the vanishing-order criterion is
--
--   $$n\le\operatorname{ord}_z(p\circ f_c)
--   \quad\Longleftrightarrow\quad
--   (\mathcal D_c^k p)(f_c(z))=0\quad\text{for all }0\le k<n.$$
--
--   The analytic order is allowed to be infinite. These statements include $n=0$ and the zero polynomial, using degree zero for the zero polynomial.
--
--   Fix also a nondecreasing function $B:\mathbb N\to\mathbb N$ with positive values such that, for every degree bound $e$, chart $c$, polynomial $p$ of degree at most $e$, and point $v\in\mathbb C^4$, vanishing of $(\mathcal D_c^kp)(v)$ for all $k<B(e)$ is equivalent to vanishing for all $k\ge0$. This one cutoff function is fixed before the polynomial and finite-set parameters below.
--
--   For either chart, a point $v\in\mathbb C^4$ and an integer $N\ge0$, define the contact ideal
--
--   $$J_{c,v}(N)=\left\langle p\in\mathbb C[x_0,x_1,x_2,x_3] :
--   (\mathcal D_c^k p)(v)=0\text{ for every }0\le k<N\right\rangle.$$
--
--   Angle brackets mean the ideal generated by the displayed set. The definition uses the ambient four-variable polynomial ring and an arbitrary affine evaluation point. Neither the cubic equation nor a nonzero chart denominator is required.
--
--   Assume the following proved contact-ideal structure.
--
--   Write $\mathfrak m_v=\ker(\operatorname{ev}_v)$ for the maximal ideal of the affine point $v$. For the fixed invariants $g_2,g_3$ of $L$, both charts, all affine points and all nonnegative integers $M,N$, the following hold:
--
--   1. A polynomial belongs to $J_{c,v}(N)$ if and only if its jets of orders $k<N$ vanish at $v$. Thus taking the ideal span in the definition adds no further polynomials.
--   2. $J_{c,v}(M)J_{c,v}(N)\subseteq J_{c,v}(M+N)$, and $\mathfrak m_v^N\subseteq J_{c,v}(N)$.
--   3. If $N>0$, then $\sqrt{J_{c,v}(N)}=\mathfrak m_v$ and $J_{c,v}(N)$ is a primary ideal. Here primary means that the ideal is proper and that $ab$ in the ideal and $a$ outside it imply that a power of $b$ lies in the ideal.
--   4. If $v\ne w$, then $J_{c,v}(M)+J_{c,w}(N)$ is the entire polynomial ring, including when either order is zero.
--   5. $\mathcal D_c(J_{c,v}(N+1))\subseteq J_{c,v}(N)$.
--   6. For every finite set $V\subset\mathbb C^4$, orders $N_v\ge0$ and assigned polynomials $p_v$, there is one polynomial $q$ satisfying $q-p_v\in J_{c,v}(N_v)$ for every $v\in V$. Equivalently, $q$ simultaneously matches the jets of the assigned polynomials through order $N_v-1$ at each point.
--
--   The last assertion is interpolation of polynomial residue classes; no degree bound on the interpolating polynomial is asserted. The statement includes empty finite sets and zero orders. These properties give the local algebra of the contact conditions; the additional dimension hypotheses below describe their combined quotient.
--
--   There is a real constant $C>0$ uniform in integers $m,n,U\ge1$, finite sets $X\subset\mathbb C$ containing zero, and complex bihomogeneous polynomials $Q$ of bidegree $(m,n)$ in two additive and five projective coordinates. Assume that for every chart $c$ and point $z\in U_c$,
--
--   $$N_cQ\notin J_{c,f_c(z)}(B(m+2n)).$$
--
--   The normalized polynomial $N_cQ$ is defined as follows.
--
--   Write a polynomial in seven variables as $Q(Y_0,Y_1;X_0,X_1,X_2,X_3,X_4)$. Define two algebra homomorphisms into four-variable polynomial rings over $\mathbb C$ by
--
--   $$N_0Q(t,x,y,r)=Q(1,t;1,x,y,r,yr+2x^2),$$
--
--   $$N_2Q(t,a,b,d)=Q(1,t;a,b,1,ad-2b^2,d).$$
--
--   These substitutions set the additive homogenizing coordinate to one and eliminate a projective coordinate using $X_0X_4-X_2X_3-2X_1^2=0$. The subscripts denote the nonzero homogeneous coordinate, so the Lean indices `0` and `1` select $N_0$ and $N_2$, respectively.
--
--   Suppose for every $c\in\{0,2\}$ and $k\ge0$,
--
--   $$\deg(\mathcal D_c^kN_cQ)\le m+2n+k.$$
--
--   For each chart $c$, define the finite sets
--
--   $$Z_c=\{z\in X+X+X:S_c(z)\ne0\},\qquad V_c=f_c(Z_c),$$
--
--   and the ideal
--
--   $$I_c=\bigcap_{v\in V_c}J_{c,v}(3U+1)\subset A.$$
--
--   Assume for each chart that $N_cQ\in I_c$, the quotient $A/I_c$ is finite-dimensional over $\mathbb C$, and
--
--   $$\dim_{\mathbb C}(A/I_c)=(3U+1)|Z_c|.$$
--
--   For each chart put $\ell_c=(3U+1)|Z_c|$ and define the time polynomial
--
--   $$M_c(T)=\prod_{v\in V_c}(T-v_0)^{3U+1}.$$
--
--   Assume that $M_c$ is monic of degree $\ell_c$ and that there are polynomials $r_{c,1},r_{c,2},r_{c,3}\in\mathbb C[T]$, all of degree below $\ell_c$, with
--
--   $$I_c=(M_c(x_0),\ x_1-r_{c,1}(x_0),\ x_2-r_{c,2}(x_0),\ x_3-r_{c,3}(x_0)).$$
--
--   Assume also the exact membership criterion, for every $p\in A$,
--
--   $$p\in I_c\quad\Longleftrightarrow\quad
--   M_c(T)\mid p(T,r_{c,1}(T),r_{c,2}(T),r_{c,3}(T)).$$
--
--   Degree here assigns minus infinity to zero. An empty chart set has $M_c=1$, $I_c=A$ and $r_{c,i}=0$, so the assertion includes it. These generator and divisibility hypotheses replace the previous existence-and-uniqueness normal-form clause.
--
--   For the same coordinate polynomials, write $\Phi_c(p)=p(T,r_{c,1}(T),r_{c,2}(T),r_{c,3}(T))$. Assume the following exact calculation after imposing any additional polynomial equation. For every $p\in A$, set $q=\Phi_c(p)$ and $J=I_c+(p)$. There exists a complex algebra isomorphism
--
--   $$A/J\simeq_{\mathbb C}\mathbb C[T]/(\gcd(M_c,q)).$$
--
--   The quotient is finite-dimensional and satisfies
--
--   $$\dim_{\mathbb C}(A/J)=\deg\gcd(M_c,q)\le\deg M_c,$$
--
--   with the further bound $\dim_{\mathbb C}(A/J)\le\deg q$ whenever $q\ne0$. This includes an identically zero added equation and empty chart sets.
--
--   Assume also that each of the above intersection lengths decomposes into local contact multiplicities. For every chart $c$ and every added equation $p$, there exist natural numbers $e_v$ for $v\in V_c$, with $e_v\le 3U+1$, such that for $0\le k\le 3U+1$,
--
--   $$k\le e_v\quad\Longleftrightarrow\quad D_c^jp(v)=0\text{ for all }0\le j<k,$$
--
--   and
--
--   $$\dim_{\mathbb C} A/(I_c+(p))=\sum_{v\in V_c}e_v.$$
--
--   The $e_v$ are the local vanishing orders truncated at the prescribed contact order $3U+1$. All previously assumed quotient isomorphisms, finite dimensionality, gcd-degree formulas, degree bounds, triangular generators and membership criteria continue to hold for the same coordinate polynomials. This added identity is supplied by the proved local-multiplicity lemma; it places no additional restriction on the point set or the added equation.
--
--   Assume in addition that the derivatives below the existing cutoff have a finite Bézout certificate in each contact quotient. Put $p_c=D_c^0\operatorname{Normalize}_c(Q)$ and $K=B(m+2n)$. For every chart there are coefficient polynomials $a_0,\ldots,a_{K-1}\in A$ with
--
--   $$1-\sum_{j<K}a_jD_c^jp_c\in I_c,$$
--
--   and
--
--   $$I_c+(D_c^jp_c:0\le j<K)=A.$$
--
--   This certificate follows from the existing nonzero-jet hypothesis, the containment of powers of point-evaluation kernels in contact ideals, and their finite Chinese remainder property. All previous finite lengths, triangular presentations, quotient isomorphisms, degree bounds and sums of local multiplicities remain in force.
--
--   Assume that the finite derivative certificate can be chosen with bounded coefficients in the time coordinate. For each chart put $d_c=(3U+1)|Z_c|$ and $K=B(m+2n)$. There are univariate polynomials $b_k$, $0\le k<K$, such that
--
--   $$\deg b_k<d_c,\qquad \operatorname{totaldeg}E(b_k)\le d_c\mathbin{\dot-}1,$$
--
--   where $E(b)=b(t)$ and natural subtraction is truncated at zero. For $p_c=\operatorname{Normalize}_c(Q)$, the residual polynomial
--
--   $$R_c=1-\sum_{k<K}E(b_k)D_c^kp_c$$
--
--   belongs to $I_c$ and satisfies
--
--   $$\operatorname{totaldeg}R_c\le(d_c\mathbin{\dot-}1)+m+2n+(K\mathbin{\dot-}1).$$
--
--   This is supplied by reducing the earlier coefficient polynomials modulo the same monic $M_c$ in the same time presentation. Every earlier certificate, unit-ideal equality, finite length, triangular presentation, intersection isomorphism and local multiplicity sum remains in force. The coefficient bound depends on the contact length $d_c$; an estimate independent of the contact data is not asserted.
--
--   Assume also the exact intersection-length formula for every initial segment of derivatives of $p_c=\operatorname{Normalize}_c(Q)$. For each chart and each natural number $s$, put
--
--   $$J_{c,s}=I_c+(p_c,D_cp_c,\ldots,D_c^{s-1}p_c),$$
--
--   where $J_{c,0}=I_c$. Then $A/J_{c,s}$ is finite-dimensional. There exist integers $0\le e_{c,s,v}\le 3U+1$ such that, for $0\le k\le3U+1$,
--
--   $$k\le e_{c,s,v}\quad\Longleftrightarrow\quad D_c^{j+i}p_c(v)=0\quad\text{for every }0\le i<s\text{ and }0\le j<k,$$
--
--   and
--
--   $$\dim_{\mathbb C}(A/J_{c,s})=\sum_{v\in V_c}e_{c,s,v}.$$
--
--   These formulas use the same contact ideals and the same normalized polynomial. Every previous certificate, degree bound, time presentation, one-equation quotient isomorphism and local multiplicity formula is retained. No bound on the number of strict stages is assumed.
--
--   Assume moreover an explicit description using the first nonzero jet orders. In each chart there are integers $t_v$ with
--
--   $$3U+1\le t_v<B(m+2n),\qquad D_c^{t_v}p_c(v)\ne0,\qquad D_c^jp_c(v)=0\quad(0\le j<t_v).$$
--
--   For every positive $s$, the same ideals $J_{c,s}$ defined above are finite-dimensional quotients with
--
--   $$\dim_{\mathbb C}(A/J_{c,s})=\sum_{v\in V_c}\min\{3U+1,\max(t_v+1-s,0)\}.$$
--
--   Also
--
--   $$J_{c,s}=A\quad\Longleftrightarrow\quad t_v<s\ \text{for every }v\in V_c,$$
--
--   and in particular $J_{c,s}=A$ whenever $B(m+2n)\le s$. The same $t_v$ work for all positive $s$. The earlier common-jet formulations for all $s\ge0$ remain in force. These conclusions use the existing cutoff and do not give a degree bound for that cutoff.
--
--   Strengthen the common-jet description of each derivative-prefix intersection to equality of ideals. For every chart and every $s\ge0$, the same residual common-jet orders $e_{c,s,v}$ in that description also satisfy
--
--   $$J_{c,s}=\bigcap_{v\in V_c}C_c(v,e_{c,s,v}).$$
--
--   Thus the equations generate exactly the residual contact intersection, in addition to having the stated quotient length. All previous common-jet equivalences, explicit first-order profiles, stopping criteria and length formulas remain in force. The factors of positive order have the primary support already given by the contact-ideal structure hypotheses; order-zero factors are the whole ring.
--
--   For each derivative-prefix stage, also identify the radical and every prime ideal containing its residual intersection:
--
--   $$\sqrt{J_{c,s}}=\bigcap_{\substack{v\in V_c\\e_{c,s,v}>0}}\mathfrak m_v,$$
--
--   and for every prime ideal $P\subseteq A$,
--
--   $$J_{c,s}\subseteq P\quad\Longleftrightarrow\quad\text{there is a unique }v\in V_c\text{ with }e_{c,s,v}>0\text{ and }P=\mathfrak m_v.$$
--
--   Here $\mathfrak m_v=\ker(\operatorname{ev}_v)$ and the same residual orders and ideals from the contact decomposition are used. These conclusions include empty support. All earlier contact decompositions, common-jet equivalences, explicit profiles, stopping criteria and length formulas remain in force.
--
--   For every derivative-prefix stage, also identify the complex algebra of its residual intersection:
--
--   $$A/J_{c,s}\ \cong_{\mathbb C}\ \prod_{v\in V_c}\mathbb C[T]\big/\big((T-v_0)^{e_{c,s,v}}\big).$$
--
--   Use the same residual orders and ideal $J_{c,s}$ as in the contact decomposition and prime-support formulas. The assertion is existence of an algebra isomorphism, so multiplication and complex scalars are preserved. It holds also at stage zero and with empty or zero-order factors. All previous common-jet equivalences, decompositions, radicals, prime classifications, profiles, stopping criteria and length formulas remain in force.
--
--   At every derivative-prefix stage, also compute the saturation of its residual ideal by every polynomial $p\in A$. Put
--
--   $$K_{c,s,p}=J_{c,s}:p^{3U+1},\qquad
--    e'_{c,s,v}=\begin{cases}0,&p(v)=0,\\e_{c,s,v},&p(v)\ne0.\end{cases}$$
--
--   Require
--
--   $$K_{c,s,p}=\bigcap_{v\in V_c}C_c(v,e'_{c,s,v})=J_{c,s}:p^\infty,$$
--
--   and require that $A/K_{c,s,p}$ is finite dimensional with
--
--   $$\dim_{\mathbb C}(A/K_{c,s,p})=\sum_{\substack{v\in V_c\\p(v)\ne0}}e_{c,s,v}.$$
--
--   Use the same residual orders as in the contact decomposition; their existing bound $e_{c,s,v}\le3U+1$ supplies the stated exponent. These requirements include stage zero, empty support and the zero polynomial. All previous algebra models, common-jet equivalences, decompositions, radicals, prime classifications, profiles, stopping criteria and lengths remain in force.
--
--   For each chart's finite contact ideal $I_c$ and every additional hypersurface polynomial $p\in A$, also compute the residual ideal using the same time presentation. With $q=\Phi_{r_c}(p)$, put
--
--   $$R_{c,p}=I_c:p,\qquad G_{c,p}=M_c/\gcd(M_c,q).$$
--
--   Require the exact membership test
--
--   $$f\in R_{c,p}\quad\Longleftrightarrow\quad G_{c,p}\mid\Phi_{r_c}(f),$$
--
--   an isomorphism of complex algebras
--
--   $$A/R_{c,p}\cong_{\mathbb C}\mathbb C[T]/(G_{c,p}),$$
--
--   and finite dimensionality with
--
--   $$\dim_{\mathbb C}(A/R_{c,p})=\deg G_{c,p},$$
--
--   $$\dim_{\mathbb C}(A/R_{c,p})+\dim_{\mathbb C}(A/(I_c+(p)))=\deg M_c.$$
--
--   These residual requirements use the same $M_c$, $r_c$, and hypersurface quotient as the existing intersection formulas. They include $p=0$ and empty contact sets. All earlier residual-stage saturation results, algebra models, common-jet equivalences, decompositions, radicals, prime classifications, profiles, stopping criteria and lengths remain in force.
--
--   For every additional hypersurface polynomial $p$, require the same truncated jet orders $e_v$ used in its intersection-length formula to describe the residual ideal as well. Writing $N=3U+1$, this adds
--
--   $$I_c:p=\bigcap_{v\in V_c}C_c(v,N-e_v),\qquad
--   \dim_{\mathbb C}(A/(I_c:p))=\sum_{v\in V_c}(N-e_v).$$
--
--   These orders are the existing witnesses satisfying $e_v\le N$ and the full truncated-jet equivalence for $p$; they are not new independent witnesses. The previous residual quotient algebra, its finite dimensionality and its length balance remain part of the premise. The decomposition also includes $p=0$ and empty contact sets. All preceding data and the final global conclusion are retained.
--
--   For each additional hypersurface $p$, its intersection ideal $J=I_c+(p)$ and residual ideal $R=I_c:p$ must also be mutual residuals inside the same contact scheme:
--
--   $$I_c:R=J,\qquad I_c:J=R.$$
--
--   Here the colon by an ideal means $I_c:K=\{f\in A:fK\subseteq I_c\}$. These are ideal equalities using the same $I_c,J,R$ as the existing algebra, length and complementary-contact formulas. All earlier data and the final global conclusion remain in force.
--
--   Write $Q_c$ for the normalized chart polynomial. At every derivative-prefix stage $s\ge0$, the intersection ideal
--
--   $$J_s=I_c+(Q_c,D_cQ_c,\ldots,D_c^{s-1}Q_c)$$
--
--   also has a canonical time generator: require a monic divisor $g_s$ of the same $M_c$ such that
--
--   $$\deg g_s\le\deg M_c,\qquad J_s=I_c+(E(g_s)),$$
--
--   $$f\in J_s\quad\Longleftrightarrow\quad g_s\mid\Phi_{r_c}(f),\qquad
--   \dim_{\mathbb C}(A/J_s)=\deg g_s.$$
--
--   Require uniqueness among all monic polynomials giving that exact membership test. At $s=0$ the derivative family is empty. This generator is compatible with all the existing finite-dimensionality, contact-order, algebra-product, support, saturation and length data; every earlier clause and the global conclusion remain unchanged.
--
--   At every derivative-prefix stage $s\ge0$, take the residual by the whole intersection ideal,
--
--   $$J_s=I_c+(Q_c,D_cQ_c,\ldots,D_c^{s-1}Q_c),\qquad R_s=I_c:J_s.$$
--
--   Require $I_c\subseteq R_s$, $I_c:R_s=J_s$, and finite dimensionality of $A/R_s$, with
--
--   $$\dim_{\mathbb C}(A/R_s)+\dim_{\mathbb C}(A/J_s)=\deg M_c.$$
--
--   For every ideal $K$ containing $I_c$, also require
--
--   $$J_s\subseteq K\quad\Longleftrightarrow\quad I_c:K\subseteq R_s.$$
--
--   Here $Q_c$ is the normalized chart polynomial and the derivative family is empty when $s=0$. All canonical generator, contact-order, algebra, support, saturation and length clauses continue to hold with the same data. Every earlier premise and the global conclusion remain unchanged.
--
--   At every derivative-prefix stage, use the same contact-order witnesses $e_v$ already specifying
--
--   $$J_s=\bigcap_{v\in V_c}C_v(e_v),\qquad 0\le e_v\le N,\qquad N=3U+1.$$
--
--   Require an exact contact decomposition and length for the residual by the whole intersection ideal:
--
--   $$I_c:J_s=\bigcap_{v\in V_c}C_v(N-e_v),\qquad
--   \dim_{\mathbb C}(A/(I_c:J_s))=\sum_{v\in V_c}(N-e_v).$$
--
--   The residual is the same one already appearing in the involution, inclusion and complementary-length clauses. These additional equalities use the existing contact-order witnesses at each $s$, including the empty derivative prefix. All earlier hypotheses and the final zero-estimate conclusion remain unchanged.
--
--   For every derivative-prefix intersection $J_s$ and its residual $R_s=I_c:J_s$, use the same contact orders $e_v$ and $N=3U+1$ to require
--
--   $$J_s+R_s=\bigcap_{v\in V_c}C_v(\min(e_v,N-e_v)).$$
--
--   Require finite dimensionality of its quotient, with
--
--   $$\dim_{\mathbb C}(A/(J_s+R_s))=\sum_{v\in V_c}\min(e_v,N-e_v),$$
--
--   and the exact comaximality criterion
--
--   $$J_s+R_s=A\quad\Longleftrightarrow\quad
--   \text{for every }v\in V_c,\quad e_v=0\text{ or }e_v=N.$$
--
--   These statements measure the overlap of each intersection with its residual, using the already specified contact decompositions. They hold also for the empty derivative prefix. Every earlier hypothesis and the final zero-estimate conclusion remain unchanged.
--
--   At each derivative-prefix stage, when every existing contact order is an endpoint,
--
--   $$\text{for every }v\in V_c,\qquad e_v=0\text{ or }e_v=N,\qquad N=3U+1,$$
--
--   require that the ideal $J_s$ and its residual $R_s=I_c:J_s$ split the original contact ideal and its quotient:
--
--   $$J_s\cap R_s=I_c,\qquad J_sR_s=I_c,\qquad
--   A/I_c\cong(A/J_s)\times(A/R_s)$$
--
--   as complex algebras. Also require a polynomial $p$ with
--
--   $$p\in J_s,\qquad 1-p\in R_s,\qquad p^2-p\in I_c,$$
--
--   $$J_s=I_c+(p),\qquad R_s=I_c+(1-p).$$
--
--   This is conditional on the endpoint criterion already equivalent to $J_s+R_s=A$; no endpoint assumption is imposed on other stages. All earlier hypotheses, witnesses and the final zero-estimate conclusion remain unchanged.
--
--   At every derivative-prefix stage put $R_s=I_c:J_s$ and $K_s=J_s\cap R_s$, using the same contact orders $e_v$ and $N=3U+1$. Require
--
--   $$I_c\subseteq K_s,\qquad K_s^2\subseteq I_c,\qquad
--   K_s=\bigcap_{v\in V_c}C_v\bigl(\max(e_v,N-e_v)\bigr).$$
--
--   The quotient $A/K_s$ is finite dimensional, with
--
--   $$\dim_{\mathbb C}(A/K_s)=\sum_{v\in V_c}\max(e_v,N-e_v),$$
--
--   $$\dim_{\mathbb C}(A/K_s)+\dim_{\mathbb C}(A/(J_s+R_s))=\dim_{\mathbb C}(A/I_c).$$
--
--   Also require $K_s=I_c$ if and only if $J_s+R_s=A$. These statements apply to every prefix, including those with overlapping residual support. The previous conditional product splitting and all earlier hypotheses, witnesses and the final zero-estimate conclusion are retained.
--
--   At every derivative-prefix stage, retain the existing contact presentation
--
--   $$J_s=\bigcap_{v\in V_c}C_v(e_v).$$
--
--   For every nonnegative order function $f:V_c\to\mathbb N$, put
--   $K_f=\bigcap_v C_v(f_v)$ and require
--
--   $$J_s\subseteq K_f\Longleftrightarrow\forall v,\ f_v\le e_v,$$
--
--   $$J_s=K_f\Longleftrightarrow e=f,$$
--
--   $$J_s\subsetneq K_f\Longleftrightarrow
--   (\forall v,\ f_v\le e_v)\text{ and }(\exists v,\ f_v<e_v).$$
--
--   These comparisons use the same witnesses $e_v$ already describing the
--   prefix ideal, and prove their uniqueness among all contact presentations
--   on $V_c$. The test function $f$ is arbitrary; it is not restricted by the
--   full contact order. All earlier hypotheses, witnesses and the final
--   zero-estimate conclusion are retained.
--
--   At every derivative-prefix stage, whenever the existing ideal $J_s$ is
--   proper, require a polynomial whose derivative leaves that ideal:
--
--   $$J_s\ne A\quad\Longrightarrow\quad
--   \exists p\in A,\ p\in J_s\text{ and }D_c(p)\notin J_s.$$
--
--   This uses the finite-dimensional quotient $A/J_s$ already supplied at
--   that stage and the chart identity $D_c(t)=1$. The witness is an arbitrary
--   polynomial in $J_s$; no new degree bound or form for it is assumed.
--   All previous hypotheses, witnesses and the final zero-estimate
--   conclusion are retained.
--
--   At every derivative-prefix stage with proper ideal $J$, additionally
--   assume a monic time polynomial $g\in\mathbb C[T]$ satisfying
--   $0<\deg g\leq\dim_{\mathbb C}(A/J)$ and
--
--   $$q(t)\in J\iff g\mid q\qquad(q\in\mathbb C[T]).$$
--
--   Its evaluation belongs to $J$, while
--   $D_c(g(t))=g'(t)\notin J$ and $\deg g'<\deg g$.
--   Here $t$ is the chart's time coordinate. This supplies a specified form
--   and a degree bound for an escaping element at every proper stage.
--   The assertion is conditional on properness, and the earlier unrestricted
--   escape assertion is retained. Every other hypothesis, witness, formula
--   and the final multiplicity estimate remain unchanged.
--
--   At every derivative-prefix stage, let $J=\bigcap_v C_v(e_v)$ be its
--   existing contact decomposition. For every $k\in\mathbb N$, additionally
--   assume that the ideal $K=J+(D_c^kq:q\in J)$ equals
--   $\bigcap_v C_v(\max(e_v-k,0))$, has finite quotient dimension
--   $\sum_v\max(e_v-k,0)$, and is the whole ring exactly when all $e_v\leq k$.
--   Also require that $p\in K$ is equivalent to the existence of $q\in J$
--   with $p-D_c^kq\in J$.
--
--   These assertions apply to all stages and derivative orders. They use
--   the already chosen exponents $e_v$ and adjoin derivatives of elements
--   ranging over the whole prefix ideal. Every earlier assumption, witness,
--   bound, escape assertion and the final multiplicity estimate is retained.
--
--   For every finite generating family $f_1,\ldots,f_{r_0}$ of each
--   derivative-prefix ideal $J$, and every $k\in\mathbb N$, additionally
--   assume that
--
--   $$K_k=(D_c^j f_i:1\leq i\leq r_0,\ 0\leq j\leq k)
--   =J+(D_c^kq:q\in J)
--   =\bigcap_v C_v(\max(e_v-k,0)).$$
--
--   Its quotient is finite dimensional of dimension
--   $\sum_v\max(e_v-k,0)$; membership is equivalent to having a single
--   $k$-th primitive modulo $J$ lying in $J$; and it is the whole ring
--   exactly when all $e_v\leq k$.
--
--   This clause uses the already chosen contact exponents. It applies to
--   any family satisfying the stated generating equality. All previous
--   contact-differentiation formulas, assumptions, witnesses, escape
--   assertions and the final multiplicity estimate are retained.
--
--   For the already specified ideals $K_k$ obtained from any finite
--   generating family of each derivative-prefix ideal $J$, additionally
--   assume the following progress and stopping formulas:
--
--   $$K_k\subseteq K_{k+1},\qquad
--   K_k=K_{k+1}\ \Longleftrightarrow\ K_k=\mathbb C[t,x,y,z],$$
--
--   $$K_k\subsetneq K_{k+1}\ \Longleftrightarrow\
--   \exists v\in V_c,\ k<e_v,$$
--
--   $$\dim_{\mathbb C}(\mathbb C[t,x,y,z]/K_k)
--   =\dim_{\mathbb C}(\mathbb C[t,x,y,z]/K_{k+1})
--   +|\{v\in V_c:k<e_v\}|.$$
--
--   These clauses use the same generators and contact exponents as the
--   existing finite-generator clause. All its previous identities and all
--   other assumptions, witnesses, escape assertions and the complete final
--   multiplicity estimate are retained.
--
--   For the canonical monic divisor $g$ of $M$ already associated with each
--   derivative-prefix ideal $J$, define the four polynomials
--
--   $$f_0=g(t),\qquad f_i=x_i-r_i(t)\quad(1\leq i\leq3).$$
--
--   Additionally require that
--
--   $$J=(f_0,f_1,f_2,f_3),\qquad
--   \deg f_i\leq\max(1,\deg M),$$
--
--   and that for every $k\in\mathbb N$,
--
--   $$\deg(D_c^j f_i)\leq\max(1,\deg M)+k
--   \qquad(0\leq j\leq k,\ 0\leq i\leq3).$$
--
--   Here $M$ is monic, so its degree is a nonnegative integer; multivariate
--   degrees are total degrees, with zero assigned total degree zero. This
--   uses the same $g$ and coordinate polynomials $r_i$ as the existing
--   presentation. All earlier witnesses, generator-jet formulas, progress
--   criteria, escape assertions and the complete multiplicity estimate remain.
--
--   For the canonical monic polynomial $g$ already associated with each
--   derivative-prefix ideal $J$, additionally require the following for
--   every contact presentation $J=\bigcap_{v\in V_c} C_v(e_v)$:
--
--   $$g(T)=\prod_{v\in V_c}(T-t_v)^{e_v},\qquad t_v=v_0,$$
--
--   and, for every $z\in\mathbb C$,
--
--   $$g(z)=0\quad\Longleftrightarrow\quad
--   \exists v\in V_c:\ e_v>0\ \text{and}\ z=t_v.$$
--
--   This uses the same canonical polynomial as the existing ideal
--   presentation, four-generator list and quotient-dimension formula.
--   Every earlier witness, degree bound, generator-jet identity, progress
--   criterion, escape assertion and the complete multiplicity estimate
--   is retained.
--
--   For each derivative-prefix ideal J and its existing canonical monic time
--   polynomial g, put d=deg(g)=dim_C(A/J), t=X_0, p=g(t), and let δ be the chart
--   derivation. Require also the explicit identities
--   δ^k(p)=g^(k)(t) for every k, δ^d(p)=d!, and (d!)^(-1)δ^d(p)=1.
--   All derivatives above d vanish, and for each k≥dim_C(A/J), the ideal
--   generated by p,δp,...,δ^k(p) is the unit ideal. This uses derivatives of the
--   single canonical time polynomial. These assertions are added to its
--   existing membership, dimension, factorization and uniqueness data.
--
--   For each derivative-prefix ideal $J$ and its existing canonical monic time
--   polynomial $g$, require the following update rule for every $p\in A$.
--   Write $\phi$ for the existing triangular coordinate substitution,
--   $h=\gcd(g,\phi(p))$ and $K=J+(p)$. Then $h$ is monic, divides $g$, and
--   is the unique monic polynomial with membership criterion
--   $f\in K\iff h\mid\phi(f)$. The quotient $A/K$ is finite dimensional,
--   with dimension $\deg h\leq\deg g$. Also $h=g$ precisely when $p\in J$;
--   both the polynomial degree and the quotient dimension strictly decrease
--   precisely when $p\notin J$. This applies in particular when the adjoined
--   equation is the next derivative of the normalized polynomial.
--
--   For each chart, write $\phi$ for the existing triangular substitution and
--   $P$ for the normalized polynomial. The canonical polynomial $g$ of the
--   derivative-prefix ideal of length $s$ is required to equal $G_s$, where
--
--   $$G_0=M,\qquad G_{j+1}=\gcd(G_j,\phi(\delta^jP)).$$
--
--   Thus the canonical polynomials already occurring in the hypotheses are
--   the values of this explicit recurrence. All their previous properties
--   and the final multiplicity estimate are retained.
--
--   For each chart and each derivative prefix $s$, write $p_j=D_c^jQ_c$, $J_j=I+(p_0,\ldots,p_{j-1})$, and $T_s=\{j<s:p_j\notin J_j\}$. The contact data also satisfy
--   $$J_s=I+(p_j:j\in T_s),\qquad
--   |T_s|+\dim_{\mathbb C}(A/J_s)\leq\deg M.$$
--   In particular the derivatives that changed the ideal when first adjoined suffice to generate the prefix modulo $I$, and their number is bounded by the loss of quotient dimension. All canonical polynomial, recurrence, update, certificate, factorization and contact conditions stated above remain in force.
--
--   For each chart and derivative prefix $s$ with $J_s=A$, the retained indices $T_s=\{j<s:p_j\notin J_j\}$ also support a bounded Bézout certificate. There are polynomials $b_j(t)$, indexed by $j\in T_s$, with $\deg b_j<\deg M$ and $\deg_{\rm tot}b_j(x_0)\leq\deg M-1$, such that
--   $$1-\sum_{j\in T_s}b_j(x_0)p_j\in I.$$
--   The same coefficients satisfy
--   $$\deg_{\rm tot}\left(1-\sum_{j\in T_s}b_j(x_0)p_j\right)\leq\deg M-1+D$$
--   for every natural number $D$ bounding the total degrees of all retained derivatives. Subtraction by $1$ is truncated in the natural-number bounds. The earlier sparse-generator inequality already bounds $|T_s|$ by $\deg M$. This applies in particular at the existing uniform unit-ideal cutoff. All previous conditions remain in force.
--
--   For every chart and every positive derivative prefix $s$ with $J_s=A$, there is an integer $a$ with $0\leq a\leq |V|(s-1)$ such that
--   $$q=\sum_{j=0}^{s-1}a^jD_c^jQ_c$$
--   is nonzero at each contact point in $V$ and satisfies
--   $$\deg_{\rm tot}q\leq m+2n+s-1.$$
--   The coefficients in this combination are constants, and $a^0=1$ also when $a=0$. This applies in particular at the existing positive uniform unit-ideal cutoff. All earlier contact, canonical polynomial, sparse certificate and multiplicity conditions remain in force.
--
--   For the same bounded integer parameter $a$ and generic combination $q=\sum_{j<s}a^jD_c^jQ_c$ at every positive unit derivative prefix, additionally require a polynomial $b\in\mathbb C[T]$ with degree below $d=\deg M$ such that $1-E(b)q\in I$. Its time lift has total degree at most $d-1$, and the residual $1-E(b)q$ has total degree at most $d-1+\deg_{\rm tot}q$. This $b$ is unique among polynomials of degree below $d$ satisfying the congruence. Multiplication by $q$ is cancellable modulo $I$: $fq\in I$ if and only if $f\in I$ for every polynomial $f$. Also $I+(q)=A$. Here $E$ substitutes the time coordinate for the univariate variable and $d-1$ is truncated natural subtraction. These conditions supplement the same parameter bound, nonvanishing and total-degree bound already required of $q$.
--
--   For the same generic combination $q$ and its bounded inverse $b$ at each positive unit derivative prefix, additionally require a complex-linear map $T:A\to\mathbb C[t]$ given by $T(p)=\phi(pE(b))\bmod M$. Here $\phi$ is the existing time substitution and $E$ lifts a univariate polynomial to the time coordinate. Writing $d=\deg M$, every $T(p)$ has degree below $d$, its lift has total degree at most $d-1$, and $p-E(T(p))q\in I$ has total degree at most $\max\{\deg_{\rm tot}p,d-1+\deg_{\rm tot}q\}$. Each $T(p)$ is the unique polynomial of degree below $d$ satisfying that congruence. Also $T(p)=0$ if and only if $p\in I$, and $T$ is the unique complex-linear map whose outputs have degree below $d$ and satisfy the congruence for all inputs. Natural subtraction is truncated. All earlier properties of the same parameter, combination and inverse remain required.
--
--   For the same generic combination $q$ and bounded division operator $T$ at each positive unit derivative prefix, additionally require a basis $\beta$ of $A/I$ indexed by $0\leq i<d=\deg M$, with $\beta_i=[x_0^i q]$. The displayed representatives have total degree at most $d-1+\deg_{\rm tot}q$. The coordinate of $[p]$ at $i$ is the coefficient $[t^i]T(p)$, so $[p]=\sum_{i<d}[t^i]T(p)\,[x_0^i q]$, and $\dim_{\mathbb C}(A/I)=d$. Natural subtraction is truncated. All earlier properties of the same parameter, combination, inverse and division operator remain required.
--
--   For the same weighted basis $\beta$ and division operator at each positive unit derivative prefix, additionally require a complex-algebra homomorphism $\rho:A\to\operatorname{Mat}_d(\mathbb C)$, where $d=\deg M$, representing multiplication by residue classes in that basis. Its entry at $(i,j)$ is $[t^i]((\phi(p)t^j)\bmod M)$, and $\rho(p)=0$ if and only if $p\in I$. With $C=\rho(x_0)$, require $\rho(p)=\phi(p)(C)$ for every $p$ and characteristic polynomial $\det(t\,1_d-C)=M(t)$. Here $\phi$ is the same existing time substitution. All earlier data, witnesses and bounds remain required.
--
--   The same quotient multiplication representation also satisfies, for every chart polynomial $p$,
--   $$\det\rho(p)=\prod_{v\in V_c}p(v)^{3U+1}.$$
--   In addition, $\rho(p)$ is invertible if and only if $p(v)\ne0$ at every contact point of positive multiplicity. Here every multiplicity is $3U+1>0$. This determinant formula and criterion hold at each positive derivative prefix whose generated ideal is the whole ring, using the same generic combination, division operator, weighted basis and representation as above.
--
--   For this same multiplication representation, every chart polynomial $p$ has
--   $$\chi_{\rho(p)}(t)=\prod_{v\in V_c}(t-p(v))^{3U+1},\qquad
--   \operatorname{tr}\rho(p)=\sum_{v\in V_c}(3U+1)p(v).$$
--   The spectrum consists exactly of the contact-point values $p(v)$. The matrix is nilpotent exactly when all those values vanish, and in that case
--   $$\rho(p)^{\deg M}=0.$$
--   These statements hold at each positive derivative prefix whose generated ideal is the whole ring, using the same generic combination, division operator, weighted basis, representation and determinant formula as above.
--
--   The same representation also identifies the image of multiplication by every chart polynomial $p$ with its residual quotient:
--   $$\mathbb C[x_0,x_1,x_2,x_3]/(I:p)\simeq\operatorname{im}\rho(p).$$
--   In particular,
--   $$\operatorname{rank}\rho(p)=\dim_{\mathbb C}(A/(I:p)),\qquad
--   \dim_{\mathbb C}\ker\rho(p)=\dim_{\mathbb C}(A/(I+(p))),$$
--   and the rank plus the intersection quotient dimension is $\deg M$. Here $A=\mathbb C[x_0,x_1,x_2,x_3]$. These conclusions hold at each positive unit derivative prefix, using the same weighted basis and multiplication representation. Together with the previously stated length formulas, they compute matrix ranks and nullities from the polynomial gcd and the local contact orders.
--
--   At every positive derivative prefix whose associated intermediate ideal is the unit ideal, the same multiplication representation also has an explicit Fitting decomposition. With $d=\deg M_c$ and $T=\rho(p)$, the subspaces $\ker T^d$ and $\operatorname{im}T^d$ are complementary, and the contact quotient is complex-linearly isomorphic to their product. For every $N\ge d$,
--   $$\ker T^N=\ker T^d,\qquad\operatorname{im}T^N=\operatorname{im}T^d,\qquad I_c:p^N=I_c:p^d.$$
--   These conclusions hold for every affine-chart polynomial $p$, with the earlier basis, rank and spectral data retained.
--
--   At every positive derivative prefix with unit intermediate ideal, the same contact quotient also has the following algebraic splitting. Set $d=\deg M_c$. For every affine-chart polynomial $p$, let
--   $$K=I_c+(p^d),\qquad R=I_c:p^d.$$
--   Then $K+R$ is the unit ideal and $K\cap R=KR=I_c$. There is a complex-algebra isomorphism
--   $$A/I_c\simeq(A/K)\times(A/R).$$
--   The class of $p$ has $d$th power zero in the first factor and is a unit in the second. There exists $e\in K$ with $1-e\in R$ and $e^2-e\in I_c$ such that
--   $$K=I_c+(e),\qquad R=I_c+(1-e).$$
--   All earlier basis, spectral, rank and Fitting data are retained.
--
--   At every positive derivative prefix with unit intermediate ideal, each polynomial class in the same contact quotient has a unique generalized inverse with index at most $d=\deg M_c$. Precisely, for every affine-chart polynomial $p$, write $a=[p]\in A/I_c$. There exists a unique $b\in A/I_c$ satisfying
--   $$ab^2=b,\qquad a^{d+1}b=a^d.$$
--   All earlier algebraic splitting, Fitting, rank, spectral and basis data are retained.
--
--   At each positive derivative prefix whose generated ideal is the unit
--   ideal, strengthen the existing unique generalized inverse witness b
--   for every polynomial class a in the contact quotient by the following
--   properties. With d=M.natDegree and f(x)=a*x, multiplication by a*b
--   is idempotent, has kernel ker(f^d) and range range(f^d), and equals
--   the canonical projection onto range(f^d) along ker(f^d). The element
--   a*b itself is idempotent. The same b still satisfies a*b*b=b and
--   a^(d+1)*b=a^d, and remains unique with this enriched property.
--   All prior hypotheses, witnesses and conclusions are retained.
--
--   At each positive derivative prefix generating the unit ideal, the
--   individual generalized inverses also assemble into a unique map
--   G from the polynomial ring to the contact quotient which preserves
--   zero, one and multiplication. For every polynomial p, with a its
--   quotient class and d=M.natDegree, this map satisfies
--   a*G(p)*G(p)=G(p) and a^(d+1)*G(p)=a^d.
--   All previous pointwise inverse and projector properties remain present.
--
--   At each positive derivative prefix generating the unit ideal,
--   strengthen the same unique multiplicative generalized-inverse map G
--   by the following pointwise criteria: G(p)=0 if and only if p belongs
--   to the radical of the contact ideal I, and the quotient class a of p
--   is a unit if and only if a*G(p)=1. The map still preserves zero,
--   one and multiplication and satisfies both original inverse equations.
--   All earlier witnesses, pointwise projectors and conclusions are retained.
--
--   At each positive derivative prefix generating the unit ideal,
--   strengthen the same unique multiplicative generalized-inverse map G
--   as follows. For every polynomial p, every representative r with
--   class r=G(p) in the contact quotient, and every contact point v,
--
--   $$r(v)=p(v)^{-1},\qquad
--   (p r)(v)=\begin{cases}0&p(v)=0,\\1&p(v)\ne0.\end{cases}$$
--
--   Here 0^(-1)=0. The formula quantifies over all representatives.
--   All earlier inverse equations, radical and unit criteria, projector
--   data, witnesses and conclusions are retained.
--
--   The canonical generalized inverse also determines the dimensions of
--   its multiplication projector. For every polynomial $p$ and every
--   representative $r$ of $G(p)$ in the contact quotient, set
--   $S_p=\{v\in V:p(v)\ne0\}$. In addition to the reciprocal and
--   zero-or-one residue values already supplied, one has
--   $$
--   \operatorname{rank}\rho(pr)=(3U+1)|S_p|,\qquad
--   \dim_{\mathbb C}\ker\rho(pr)=\deg M-(3U+1)|S_p|.
--   $$
--   These equalities hold for every representative of the same canonical
--   inverse. The second subtraction is in the natural numbers.
--
--   The multiplication matrix of every polynomial now has an explicit
--   dimension formula for all sufficiently high powers. Write
--   $d=\deg M$ and $S_p=\{v\in V:p(v)\ne0\}$. For every polynomial
--   $p$ and every natural $N\ge d$,
--   $$
--   \operatorname{rank}\bigl(\rho(p)^N\bigr)=(3U+1)|S_p|,\qquad
--   \dim_{\mathbb C}\ker\bigl(\rho(p)^N\bigr)
--   =d-(3U+1)|S_p|.
--   $$
--   The subtraction is in the natural numbers. These conclusions depend
--   only on $p$ and $N$; the existing canonical inverse and projector data
--   are also retained.
--
--   The multiplication matrices also have explicit generalized-eigenspace
--   dimensions at every value. For a polynomial $p$ and $z\in\mathbb C$,
--   let $V_{p,z}=\{v\in V:p(v)=z\}$. The maximal generalized eigenspace
--   of $\rho(p)$ at $z$ has dimension
--   $$
--   (3U+1)|V_{p,z}|.
--   $$
--   For every $N\ge\deg M$, the order-$N$ generalized eigenspace
--   $\ker(\rho(p)-zI)^N$ has this same dimension. Coincident values of
--   $p$ contribute the sum of the contact multiplicities of all points
--   in the fibre. The preceding rank, inverse and contact data are
--   also supplied.
--
--   For every polynomial $p$, let $W_p$ be the finite set of its distinct values on the contact points:
--   $$
--   W_p=\{p(v):v\in V_c\}.
--   $$
--   Write $E_{p,z}$ for the maximal generalized eigenspace of the multiplication matrix $\rho_c(p)$ at $z$. The strengthened data include an internal direct-sum decomposition and a linear equivalence given by summation:
--   $$
--   \mathbb C^{\deg M_c}=\bigoplus_{z\in W_p}E_{p,z},
--   \qquad
--   e_p:\prod_{z\in W_p}E_{p,z}\xrightarrow{\;\sim\;}\mathbb C^{\deg M_c},
--   \quad e_p((x_z))=\sum_{z\in W_p}x_z.
--   $$
--   Distinct contact points with equal polynomial values contribute to the same generalized eigenspace. This decomposition gives a unique spectral-component representation of every vector. All earlier assumptions and the final estimate below are retained.
--
--   For each polynomial $p$, the spectral summation equivalence $e_p$ additionally comes with endomorphisms $\Pi_{p,z}$ indexed by its distinct values $z\in W_p$ on the contact points. They recover its components and resolve the identity:
--   $$
--   \Pi_{p,z}(x)=(e_p^{-1}x)_z,\qquad
--   \Pi_{p,z}^2=\Pi_{p,z},\qquad
--   \Pi_{p,z}\Pi_{p,w}=0\quad(z\ne w),\qquad
--   \sum_{z\in W_p}\Pi_{p,z}=\operatorname{id}.
--   $$
--   Each range is the maximal generalized eigenspace of $\rho_c(p)$ at the indexed value. Every projector commutes with every polynomial multiplication endomorphism:
--   $$
--   \operatorname{range}\Pi_{p,z}=E_{p,z},\qquad
--   \Pi_{p,z}\rho_c(q)=\rho_c(q)\Pi_{p,z}\quad\text{for every polynomial }q.
--   $$
--   The coordinate equality includes the natural inclusion of $E_{p,z}$ into the ambient vector space. All the earlier data and the final multiplicity estimate below are retained.
--
--   For each polynomial $p$, the spectral projectors are further realized by elements $\varepsilon_{p,z}$ of the contact quotient algebra. If $b_c$ is the coordinate equivalence from its supplied basis, the strengthened data require
--   $$
--   L_{\varepsilon_{p,z}}=\Pi_{p,z},\qquad
--   \varepsilon_{p,z}=b_c^{-1}(\Pi_{p,z}(b_c(1))).
--   $$
--   Here $L_a$ is the regular multiplication operator in those coordinates. These quotient elements satisfy
--   $$
--   \varepsilon_{p,z}^2=\varepsilon_{p,z},\qquad
--   \varepsilon_{p,z}\varepsilon_{p,w}=0\quad(z\ne w),\qquad
--   \sum_{z\in W_p}\varepsilon_{p,z}=1.
--   $$
--   The preceding spectral decomposition, coordinate projectors and all earlier chart data are retained, together with the final multiplicity estimate below.
--
--   Write $B_c$ for the contact quotient algebra and retain the spectral idempotents $\varepsilon_{p,z}$. For every polynomial $p$, define ideals within $B_c$ by
--   $$
--   J_{p,z}=(1-\varepsilon_{p,z}).
--   $$
--   The strengthened data identify each such ideal as a multiplication annihilator and give a canonical algebra equivalence
--   $$
--   a\in J_{p,z}\quad\Longleftrightarrow\quad\varepsilon_{p,z}a=0,
--   \qquad
--   \Phi_p:B_c\xrightarrow{\;\sim\;}\prod_{z\in W_p}B_c/J_{p,z}.
--   $$
--   Its coordinates are the quotient maps, and the idempotents become the standard coordinate elements:
--   $$
--   \Phi_p(a)_z=[a]_{J_{p,z}},\qquad
--   \Phi_p(\varepsilon_{p,w})_z=
--   \begin{cases}1&z=w,\\0&z\ne w.\end{cases}
--   $$
--   The previously supplied idempotents, projector resolutions, spectral equivalences and all earlier chart data remain part of the hypotheses. The final multiplicity estimate below is retained unchanged.
--
--   Each spectral algebra factor is also identified explicitly with its maximal generalized eigenspace. Write $\mathcal B_c=A/I_c$, $J_{p,z}=(1-\varepsilon_{p,z})\subset\mathcal B_c$, and let $\beta$ denote the supplied basis of the contact quotient. For every $p$ and every $z\in W_p$, there is a complex-linear isomorphism
--   $$
--   \psi_{p,z}:\mathcal B_c/J_{p,z}\xrightarrow{\sim}
--   E^{\mathrm{gen}}_z(\rho(p))
--   $$
--   such that, in the ambient coordinate space,
--   $$
--   \psi_{p,z}([a])=\beta^{\mathrm{coord}}(\varepsilon_{p,z}a).
--   $$
--   Its dimension is
--   $$
--   \dim_{\mathbb C}(\mathcal B_c/J_{p,z})
--   =(3U+1)\,\bigl|\{v\in V_c:p(v)=z\}\bigr|.
--   $$
--   Here $V_c$ is the finite set of chart-coordinate points, so the cardinality counts coordinate points with the specified polynomial value. The canonical product equivalence, its quotient-map coordinates and idempotent images, and all earlier chart data are retained. The final multiplicity estimate and its subgroup restrictions are unchanged.
--
--   The action of $p$ in every spectral algebra factor is a scalar plus a nilpotent element with an explicit vanishing exponent. Write $\mathcal B_c=A/I_c$, $J_{p,z}=(1-\varepsilon_{p,z})$, and $d=\deg M_c$. For every $p$ and $z\in W_p$, the class $\overline p_{p,z}\in\mathcal B_c/J_{p,z}$ satisfies
--   $$
--   \bigl(\overline p_{p,z}-z\cdot1_{\mathcal B_c/J_{p,z}}\bigr)^d=0.
--   $$
--   The factor equivalence with its maximal generalized eigenspace, its representative formula and exact dimension, and the canonical algebra product decomposition all remain present. The exponent $d$ is the supplied dimension of the ambient contact-coordinate space. All earlier chart data and the final multiplicity estimate are retained.
--
--   The vanishing exponent in each spectral factor can be bounded by that factor's own dimension. For a polynomial $p$ and a spectral value $z\in W_p$, put
--   $$
--   d_{p,z}=(3U+1)\,\bigl|\{v\in V_c:p(v)=z\}\bigr|
--   =\dim_{\mathbb C}(\mathcal B_c/J_{p,z}),
--   \qquad J_{p,z}=(1-\varepsilon_{p,z}).
--   $$
--   Then for every integer $N\ge d_{p,z}$,
--   $$
--   \bigl(\overline p_{p,z}-z\cdot1_{\mathcal B_c/J_{p,z}}\bigr)^N=0.
--   $$
--   The previous vanishing relation at the ambient dimension is retained, as are the factor equivalences, representative formulas, exact dimensions, algebra product maps and all earlier chart data. The final multiplicity estimate and subgroup restrictions are unchanged.
--
--   Each spectral algebra factor additionally carries an explicit inverse away from its indexed spectral value. Write $\mathcal A_{p,z}=\mathcal B_c/(1-\varepsilon_{p,z})$, let $\pi_{p,z}:A\to\mathcal A_{p,z}$ be the composite quotient map, and put
--   $$
--   d_{p,z}=(3U+1)\,\bigl|\{v\in V_c:p(v)=z\}\bigr|.
--   $$
--   For every $w\in\mathbb C$ with $w\ne z$, set
--   $$
--   b_{p,z,w}=\pi_{p,z}\bigl((z-w)^{-1}\bigr)
--   \sum_{j=0}^{d_{p,z}-1}
--   \left[-\pi_{p,z}\bigl((z-w)^{-1}\bigr)\pi_{p,z}(p-z)\right]^j.
--   $$
--   Here constants inside $\pi_{p,z}$ mean constant polynomials. Then
--   $$
--   \pi_{p,z}(p-w)b_{p,z,w}=b_{p,z,w}\pi_{p,z}(p-w)=1,
--   \qquad \pi_{p,z}(p-w)\in\mathcal A_{p,z}^{\times}.
--   $$
--   The sum is truncated at the factor's own dimension. The existing nilpotence relations, factor equivalences, dimensions, product maps and all earlier chart data remain present. The final multiplicity estimate and its subgroup restrictions are unchanged.
--
--   Polynomial evaluation in every spectral factor additionally has an exact unit and nilpotence criterion. For a polynomial $p$ in the chart coordinates and a spectral value $z\in W_p$, write $\mathcal A_{p,z}=\mathcal B_c/(1-\varepsilon_{p,z})$, let $\pi:A\to\mathcal A_{p,z}$ be the composite quotient map, and put
--   $$
--   d_{p,z}=(3U+1)\,\bigl|\{v\in V_c:p(v)=z\}\bigr|.
--   $$
--   For every univariate polynomial $q\in\mathbb C[T]$, evaluate its coefficients through the scalar map $u\mapsto\pi(C(u))$. Then
--   $$
--   \bigl(q(\pi(p))-\pi(C(q(z)))\bigr)^{d_{p,z}}=0,
--   $$
--   and
--   $$
--   q(\pi(p))\in\mathcal A_{p,z}^{\times}\quad\Longleftrightarrow\quad q(z)\ne0,
--   \qquad
--   q(\pi(p))\text{ is nilpotent}\quad\Longleftrightarrow\quad q(z)=0.
--   $$
--   The spectral value $z$ has a nonempty evaluation fiber, so the factor has positive dimension. All previous resolvent formulas, nilpotence bounds, factor equivalences, dimensions, product maps and chart data remain present. The final multiplicity estimate and subgroup restrictions are unchanged.
--
--   The factor $|Z_c|$ counts the actual complex points in that chart: the first coordinate of $f_c(z)$ is $z$, so $f_c$ is injective. Empty chart sets are allowed. Under these hypotheses,
--
--   there are an additive subgroup $H\subseteq G_\eta$ and nonnegative integers $a,b$ with $b\le2$, such that either $a=1$ and $H\subseteq\ker p_a$, or $a=0$ and $H\subseteq\ker p_E$, and
--
--   $$(U+1)|q_H(\varphi(X))|\le Cm^an^b.$$
--
--   Here $p_a(t,[(z,u)])=t$, $p_E(t,[(z,u)])=z\bmod\Lambda$, and $q_H$ is the additive quotient map. The triple-sumset vanishing is expressed as membership in an intersection of contact ideals, together with its exact complex quotient dimension. The map takes values in the part of the explicit projective algebraic locus covered by the two standard affine charts with coordinate indices zero and two. The explicit additive action and its fibers are supplied, and the parametrization is bijective and equivariant, and its derivatives are supplied in both projective charts. Identification with an algebraic-group embedding, the geometric multiplicity bound and subgroup projection profiles remain open obligations. The supplied bijection is between the underlying sets; topological and algebraic compatibility remain to be proved. No finiteness of subgroup intersections is assumed.
-- source:
--   Inferred specialization in the approach to Senthil Kumar K (2026), Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. In the spectral factor indexed by z, the factor-dimension power of q(p)-q(z) is zero for every univariate polynomial q; q(p) is invertible exactly when q(z) is nonzero, and nilpotent exactly when q(z) is zero. Nontriviality of the factor follows from its positive weighted evaluation-fiber dimension. The original resolvents, nilpotence bounds, factor equivalences and chart data, and the exact final multiplicity estimate are retained. This polynomial calculation is derived here, not quoted from the article. Global quantitative geometry, algebraic-group compatibility and subgroup profiles remain Open.

import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.RingTheory.Ideal.IsPrimary
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionChartLocus
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionLocus
import Mathlib.LinearAlgebra.Projectivization.Basic
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta
open scoped Pointwise
open TranscendenceTheory

open scoped Classical

theorem WeierstrassEllipticZeta.spectral_factor_polynomial_multiplicity_obstruction
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω)
    (P : GraphQuotientExtension L.lattice η ≃ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (P ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    (F : ProjectiveExtensionFiberModel L.g₂ L.g₃)
    (hP_action : ∀ (u : ℂ) (e : GraphQuotientExtension L.lattice η),
      P (e + extensionInclusion L.lattice η u) = F.action u (P e))
    (hflow :
    (∀ z : ℂ, S 0 z ≠ 0 →
      HasDerivAt (fun w => S 1 w / S 0 w) (S 2 z / S 0 z) z ∧
      HasDerivAt (fun w => S 2 w / S 0 w) (6 * (S 1 z / S 0 z) ^ 2 - L.g₂ / 2) z ∧
      HasDerivAt (fun w => S 3 w / S 0 w) (-S 1 z / S 0 z) z) ∧
    (∀ z : ℂ, S 2 z ≠ 0 →
      HasDerivAt (fun w => S 0 w / S 2 w)
        (-6 * (S 1 z / S 2 z) ^ 2 + L.g₂ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
      HasDerivAt (fun w => S 1 w / S 2 w)
        (-(1 / 2 : ℂ) - L.g₂ * (S 0 z / S 2 z) * (S 1 z / S 2 z) -
          3 * L.g₃ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
      HasDerivAt (fun w => S 4 w / S 2 w)
        (-2 * L.g₂ * (S 1 z / S 2 z) ^ 2 -
          3 * L.g₃ * (S 0 z / S 2 z) * (S 1 z / S 2 z)) z))
    (hjets :
    (∀ c : Fin 2, extensionChartDerivation L.g₂ L.g₃ c (extensionChartCubic L.g₂ L.g₃ c) = 0) ∧
    ∀ (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ) (n : ℕ),
      ((extensionChartDerivation L.g₂ L.g₃ c)^[n] p).totalDegree ≤ p.totalDegree + n ∧
      ∀ z : ℂ, S (extensionChartDenominator c) z ≠ 0 →
        iteratedDeriv n (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z =
          MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation L.g₂ L.g₃ c)^[n] p) ∧
        ((n : ℕ∞) ≤ analyticOrderAt
            (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z ↔
          ∀ k < n, MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0))
    (B : ℕ → ℕ)
    (hB : Monotone B ∧ (∀ d : ℕ, 0 < B d) ∧
      ∀ (d : ℕ) (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ), p.totalDegree ≤ d →
        ∀ v : Fin 4 → ℂ,
          ((∀ k < B d, MvPolynomial.eval v ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0) ↔
            ∀ k : ℕ, MvPolynomial.eval v ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0))
    (hcontact :
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal L.g₂ L.g₃ c v n ↔
        ∀ k < n, MvPolynomial.eval v ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (m n : ℕ),
      extensionChartContactIdeal L.g₂ L.g₃ c v m * extensionChartContactIdeal L.g₂ L.g₃ c v n ≤
        extensionChartContactIdeal L.g₂ L.g₃ c v (m + n)) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ),
      RingHom.ker (MvPolynomial.eval v) ^ n ≤ extensionChartContactIdeal L.g₂ L.g₃ c v n) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ), 0 < n →
      (extensionChartContactIdeal L.g₂ L.g₃ c v n).radical = RingHom.ker (MvPolynomial.eval v) ∧
        (extensionChartContactIdeal L.g₂ L.g₃ c v n).IsPrimary) ∧
    (∀ (c : Fin 2) (v w : Fin 4 → ℂ), v ≠ w → ∀ m n : ℕ,
      extensionChartContactIdeal L.g₂ L.g₃ c v m ⊔ extensionChartContactIdeal L.g₂ L.g₃ c w n = ⊤) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal L.g₂ L.g₃ c v (n + 1) →
        extensionChartDerivation L.g₂ L.g₃ c p ∈ extensionChartContactIdeal L.g₂ L.g₃ c v n) ∧
    (∀ (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (n : V → ℕ)
        (p : V → MvPolynomial (Fin 4) ℂ),
      ∃ q : MvPolynomial (Fin 4) ℂ, ∀ v : V,
        q - p v ∈ extensionChartContactIdeal L.g₂ L.g₃ c v.val (n v))) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
      1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
      0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (∀ (c : Fin 2) (z : ℂ), S (extensionChartDenominator c) z ≠ 0 →
          extensionChartNormalize c Q ∉ extensionChartContactIdeal L.g₂ L.g₃ c
            (extensionChartCoordinates S c z) (B (m + 2 * n))) →
        (∀ (c : Fin 2) (k : ℕ),
          ((extensionChartDerivation L.g₂ L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
            m + 2 * n + k) →
        (∀ c : Fin 2,
          let Z := (X + X + X).filter (fun z => S (extensionChartDenominator c) z ≠ 0)
          let V := Z.image (extensionChartCoordinates S c)
          let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
            ⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (3 * U + 1)
          extensionChartNormalize c Q ∈ I ∧
            (∃ a : Fin (B (m + 2 * n)) → MvPolynomial (Fin 4) ℂ,
              1 - ∑ k : Fin (B (m + 2 * n)), a k *
                ((extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q)) ∈ I ∧
              I ⊔ Ideal.span (Set.range (fun k : Fin (B (m + 2 * n)) =>
                (extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q))) = ⊤) ∧
            FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) ∧
            Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = (3 * U + 1) * Z.card ∧
            let M : Polynomial ℂ :=
              ∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ (3 * U + 1)
            M.Monic ∧ M.degree = ((3 * U + 1) * Z.card : ℕ) ∧
            ∃ r : Fin 3 → Polynomial ℂ,
              (∀ i, (r i).degree < ((3 * U + 1) * Z.card : ℕ)) ∧
              I = Ideal.span (insert (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) M)
                (Set.range (fun i : Fin 3 => MvPolynomial.X i.succ -
                  Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (r i)))) ∧
              (∀ p : MvPolynomial (Fin 4) ℂ,
                p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p) ∧
              (∃ t : V → ℕ,
                (∀ v : V, 3 * U + 1 ≤ t v ∧ t v < B (m + 2 * n) ∧
                  MvPolynomial.eval v.val
                    ((extensionChartDerivation L.g₂ L.g₃ c)^[t v] (extensionChartNormalize c Q)) ≠ 0 ∧
                  ∀ j < t v, MvPolynomial.eval v.val
                    ((extensionChartDerivation L.g₂ L.g₃ c)^[j] (extensionChartNormalize c Q)) = 0) ∧
                ∀ s : ℕ, 0 < s →
                  let J := I ⊔ Ideal.span (Set.range (fun i : Fin s =>
                    (extensionChartDerivation L.g₂ L.g₃ c)^[i.val] (extensionChartNormalize c Q)))
                  FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) =
                    ∑ v : V, min (3 * U + 1) (t v + 1 - s) ∧
                  (J = ⊤ ↔ ∀ v : V, t v < s) ∧
                  (B (m + 2 * n) ≤ s → J = ⊤)) ∧
              (∀ s : ℕ,
                let J := I ⊔ Ideal.span (Set.range (fun i : Fin s =>
                  (extensionChartDerivation L.g₂ L.g₃ c)^[i.val] (extensionChartNormalize c Q)))
                (0 < s → J = ⊤ → ∃ a : ℕ, a ≤ V.card * (s - 1) ∧
                  let q := ∑ j : Fin s, MvPolynomial.C ((a : ℂ) ^ j.val) *
                    ((extensionChartDerivation L.g₂ L.g₃ c)^[j.val] (extensionChartNormalize c Q))
                  (∀ v : V, MvPolynomial.eval v.val q ≠ 0) ∧
                  q.totalDegree ≤ m + 2 * n + (s - 1) ∧
                  ∃ b : Polynomial ℂ,
                    b.degree < (M.natDegree : ℕ) ∧
                    (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) b).totalDegree ≤
                      M.natDegree - 1 ∧
                    1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q ∈ I ∧
                    (1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q).totalDegree ≤
                      M.natDegree - 1 + q.totalDegree ∧
                    (∀ b' : Polynomial ℂ, b'.degree < (M.natDegree : ℕ) →
                      1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b' * q ∈ I → b' = b) ∧
                    (∀ f : MvPolynomial (Fin 4) ℂ, f * q ∈ I ↔ f ∈ I) ∧
                    I ⊔ Ideal.span {q} = ⊤ ∧
                    ∃ T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ,
                      (∀ p : MvPolynomial (Fin 4) ℂ,
                        T p = (MvPolynomial.aeval (Fin.cons Polynomial.X r)
                          (p * Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b)) %ₘ M ∧
                        (T p).degree < (M.natDegree : ℕ) ∧
                        (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (T p)).totalDegree ≤
                          M.natDegree - 1 ∧
                        p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q ∈ I ∧
                        (p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q).totalDegree ≤
                          max p.totalDegree (M.natDegree - 1 + q.totalDegree) ∧
                        (∀ b' : Polynomial ℂ, b'.degree < (M.natDegree : ℕ) →
                          (p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b' * q ∈ I ↔ b' = T p))) ∧
                      (∀ p : MvPolynomial (Fin 4) ℂ, T p = 0 ↔ p ∈ I) ∧
                      (∀ T' : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ,
                        (∀ p : MvPolynomial (Fin 4) ℂ, (T' p).degree < (M.natDegree : ℕ) ∧
                          p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T' p) * q ∈ I) → T' = T) ∧
                      ∃ β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I),
                        (∀ i : Fin M.natDegree,
                          β i = Ideal.Quotient.mk I ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q) ∧
                          ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q).totalDegree ≤
                            M.natDegree - 1 + q.totalDegree) ∧
                        (∀ (p : MvPolynomial (Fin 4) ℂ) (i : Fin M.natDegree),
                          β.repr (Ideal.Quotient.mk I p) i = (T p).coeff i.val) ∧
                        (∀ p : MvPolynomial (Fin 4) ℂ,
                          Ideal.Quotient.mk I p = ∑ i : Fin M.natDegree,
                            (T p).coeff i.val • Ideal.Quotient.mk I
                              ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q)) ∧
                        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = M.natDegree ∧
                        ∃ ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ]
                            Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ,
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            ρ p = Algebra.leftMulMatrix β (Ideal.Quotient.mk I p)) ∧
                          (∀ (p : MvPolynomial (Fin 4) ℂ) (i j : Fin M.natDegree),
                            ρ p i j = ((MvPolynomial.aeval (Fin.cons Polynomial.X r) p *
                              Polynomial.X ^ j.val) %ₘ M).coeff i.val) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ, ρ p = 0 ↔ p ∈ I) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            ρ p = Polynomial.aeval (ρ (MvPolynomial.X (0 : Fin 4)))
                              (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)) ∧
                          (ρ (MvPolynomial.X (0 : Fin 4))).charpoly = M ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            (ρ p).det = ∏ v : V,
                              (MvPolynomial.eval v.val p) ^ (3 * U + 1)) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            IsUnit (ρ p) ↔ ∀ v : V, 0 < 3 * U + 1 →
                              MvPolynomial.eval v.val p ≠ 0) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            (ρ p).charpoly = ∏ v : V,
                              (Polynomial.X - Polynomial.C (MvPolynomial.eval v.val p)) ^
                                (3 * U + 1)) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            (ρ p).trace = ∑ v : V,
                              ((3 * U + 1 : ℕ) : ℂ) * MvPolynomial.eval v.val p) ∧
                          (∀ (p : MvPolynomial (Fin 4) ℂ) (z : ℂ),
                            z ∈ spectrum ℂ (ρ p) ↔ ∃ v : V,
                              0 < 3 * U + 1 ∧ z = MvPolynomial.eval v.val p) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            IsNilpotent (ρ p) ↔ ∀ v : V, 0 < 3 * U + 1 →
                              MvPolynomial.eval v.val p = 0) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            (∀ v : V, 0 < 3 * U + 1 → MvPolynomial.eval v.val p = 0) →
                              (ρ p) ^ M.natDegree = 0) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I.colon {p}) ≃ₗ[ℂ]
                              LinearMap.range (ρ p).mulVecLin) ∧
                            (ρ p).rank = Module.finrank ℂ
                              (MvPolynomial (Fin 4) ℂ ⧸ I.colon {p}) ∧
                            Module.finrank ℂ (LinearMap.ker (ρ p).mulVecLin) =
                              Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
                                (I ⊔ Ideal.span {p})) ∧
                            (ρ p).rank + Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
                              (I ⊔ Ideal.span {p})) = M.natDegree) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            IsCompl (LinearMap.ker ((ρ p) ^ M.natDegree).mulVecLin)
                              (LinearMap.range ((ρ p) ^ M.natDegree).mulVecLin) ∧
                            Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₗ[ℂ]
                              (LinearMap.ker ((ρ p) ^ M.natDegree).mulVecLin) ×
                                (LinearMap.range ((ρ p) ^ M.natDegree).mulVecLin)) ∧
                            ∀ N : ℕ, M.natDegree ≤ N →
                              LinearMap.ker ((ρ p) ^ N).mulVecLin =
                                LinearMap.ker ((ρ p) ^ M.natDegree).mulVecLin ∧
                              LinearMap.range ((ρ p) ^ N).mulVecLin =
                                LinearMap.range ((ρ p) ^ M.natDegree).mulVecLin ∧
                              I.colon {p ^ N} = I.colon {p ^ M.natDegree}) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            let K := I ⊔ Ideal.span {p ^ M.natDegree}
                            let R := I.colon {p ^ M.natDegree}
                            K ⊔ R = ⊤ ∧ K ⊓ R = I ∧ K * R = I ∧
                            Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ]
                              (MvPolynomial (Fin 4) ℂ ⧸ K) ×
                                (MvPolynomial (Fin 4) ℂ ⧸ R)) ∧
                            (Ideal.Quotient.mk K p) ^ M.natDegree = 0 ∧
                            IsUnit (Ideal.Quotient.mk R p) ∧
                            ∃ e : MvPolynomial (Fin 4) ℂ,
                              e ∈ K ∧ 1 - e ∈ R ∧ e * e - e ∈ I ∧
                              K = I ⊔ Ideal.span {e} ∧ R = I ⊔ Ideal.span {1 - e}) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            ∃! b : MvPolynomial (Fin 4) ℂ ⧸ I,
                              Ideal.Quotient.mk I p * b * b = b ∧
                              (Ideal.Quotient.mk I p) ^ (M.natDegree + 1) * b =
                                (Ideal.Quotient.mk I p) ^ M.natDegree ∧
                              (let a := Ideal.Quotient.mk I p
                               let f := Algebra.lmul ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) a
                               let E := Algebra.lmul ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) (a * b)
                               IsIdempotentElem (a * b) ∧ IsIdempotentElem E ∧
                                 LinearMap.ker E = LinearMap.ker (f ^ M.natDegree) ∧
                                 LinearMap.range E = LinearMap.range (f ^ M.natDegree) ∧
                                 ∃ h : IsCompl (LinearMap.range (f ^ M.natDegree))
                                     (LinearMap.ker (f ^ M.natDegree)),
                                   E = (LinearMap.range (f ^ M.natDegree)).projection
                                     (LinearMap.ker (f ^ M.natDegree)) h)) ∧
                          (∃! G : MvPolynomial (Fin 4) ℂ →*₀
                              (MvPolynomial (Fin 4) ℂ ⧸ I),
                            ∀ p : MvPolynomial (Fin 4) ℂ,
                              Ideal.Quotient.mk I p * G p * G p = G p ∧
                              (Ideal.Quotient.mk I p) ^ (M.natDegree + 1) * G p =
                                (Ideal.Quotient.mk I p) ^ M.natDegree ∧
                              (G p = 0 ↔ p ∈ I.radical) ∧
                              (IsUnit (Ideal.Quotient.mk I p) ↔
                                Ideal.Quotient.mk I p * G p = 1) ∧
                              ∀ r : MvPolynomial (Fin 4) ℂ,
                                Ideal.Quotient.mk I r = G p →
                                  (∀ v : V,
                                    MvPolynomial.eval v.val r = (MvPolynomial.eval v.val p)⁻¹ ∧
                                    MvPolynomial.eval v.val (p * r) =
                                      if MvPolynomial.eval v.val p = 0 then 0 else 1) ∧
                                  (ρ (p * r)).rank = (3 * U + 1) *
                                    (Finset.univ.filter (fun v : V =>
                                      MvPolynomial.eval v.val p ≠ 0)).card ∧
                                  Module.finrank ℂ (LinearMap.ker (ρ (p * r)).mulVecLin) =
                                    M.natDegree - (3 * U + 1) *
                                      (Finset.univ.filter (fun v : V =>
                                        MvPolynomial.eval v.val p ≠ 0)).card) ∧
                          (∀ (p : MvPolynomial (Fin 4) ℂ) (N : ℕ), M.natDegree ≤ N →
                            ((ρ p) ^ N).rank = (3 * U + 1) *
                              (Finset.univ.filter (fun v : V =>
                                MvPolynomial.eval v.val p ≠ 0)).card ∧
                            Module.finrank ℂ (LinearMap.ker ((ρ p) ^ N).mulVecLin) =
                              M.natDegree - (3 * U + 1) *
                                (Finset.univ.filter (fun v : V =>
                                  MvPolynomial.eval v.val p ≠ 0)).card) ∧
                          (∀ (p : MvPolynomial (Fin 4) ℂ) (z : ℂ),
                            Module.finrank ℂ
                              (Module.End.maxGenEigenspace (ρ p).mulVecLin z) =
                                (3 * U + 1) * (Finset.univ.filter (fun v : V =>
                                  MvPolynomial.eval v.val p = z)).card ∧
                            ∀ N : ℕ, M.natDegree ≤ N →
                              Module.finrank ℂ
                                (Module.End.genEigenspace (ρ p).mulVecLin z N) =
                                  (3 * U + 1) * (Finset.univ.filter (fun v : V =>
                                    MvPolynomial.eval v.val p = z)).card) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            let W := Finset.univ.image (fun v : V => MvPolynomial.eval v.val p)
                            DirectSum.IsInternal (fun z : W =>
                              Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ∧
                            ∃ e : (∀ z : W,
                                Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ≃ₗ[ℂ]
                                  (Fin M.natDegree → ℂ),
                              (∀ x, e x = ∑ z : W, (x z : Fin M.natDegree → ℂ)) ∧
                              ∃ Pr : W → Module.End ℂ (Fin M.natDegree → ℂ),
                                (∀ z x, Pr z x = (e.symm x z : Fin M.natDegree → ℂ)) ∧
                                (∀ z, IsIdempotentElem (Pr z)) ∧
                                (∀ z w, z ≠ w → Pr z * Pr w = 0) ∧
                                (∑ z, Pr z) = 1 ∧
                                (∀ z, LinearMap.range (Pr z) =
                                  Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ∧
                                (∀ (q : MvPolynomial (Fin 4) ℂ) (z : W),
                                  Commute (Pr z) (ρ q).mulVecLin) ∧
                                ∃ ε : W → MvPolynomial (Fin 4) ℂ ⧸ I,
                                  (∀ z, (Algebra.leftMulMatrix β (ε z)).mulVecLin = Pr z) ∧
                                  (∀ z, ε z = β.equivFun.symm (Pr z (β.equivFun 1))) ∧
                                  (∀ z, IsIdempotentElem (ε z)) ∧
                                  (∀ z w, z ≠ w → ε z * ε w = 0) ∧
                                  (∑ z, ε z) = 1 ∧
                                  (∀ z (a : MvPolynomial (Fin 4) ℂ ⧸ I),
                                    a ∈ Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)) ↔ ε z * a = 0) ∧
                                  ∃ Φ : (MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ]
                                      (∀ z : W, (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                                        Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
                                    (∀ a z, Φ a z =
                                      Ideal.Quotient.mk (Ideal.span {1 - ε z}) a) ∧
                                    (∀ z w, Φ (ε w) z = if z = w then 1 else 0) ∧
                                    ∀ z : W, ∃ ψ : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                                          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) ≃ₗ[ℂ]
                                        Module.End.maxGenEigenspace (ρ p).mulVecLin z.val,
                                      (∀ a : MvPolynomial (Fin 4) ℂ ⧸ I,
                                        (ψ (Ideal.Quotient.mk (Ideal.span {1 - ε z}) a) : Fin M.natDegree → ℂ) =
                                          β.equivFun (ε z * a)) ∧
                                      Module.finrank ℂ
                                        ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                                          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) =
                                        (3 * U + 1) * (Finset.univ.filter (fun v : V =>
                                          MvPolynomial.eval v.val p = z.val)).card ∧
                                      (Ideal.Quotient.mk
                                        (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))
                                        (Ideal.Quotient.mk I (p - MvPolynomial.C z.val))) ^
                                          M.natDegree = 0 ∧
                                      (∀ N : ℕ, (3 * U + 1) *
                                        (Finset.univ.filter (fun v : V =>
                                          MvPolynomial.eval v.val p = z.val)).card ≤ N →
                                        (Ideal.Quotient.mk
                                          (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))
                                          (Ideal.Quotient.mk I (p - MvPolynomial.C z.val))) ^ N = 0) ∧
                                      (∀ w : ℂ, w ≠ z.val →
                                        let π := (Ideal.Quotient.mk
                                          (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))).comp
                                            (Ideal.Quotient.mk I)
                                        let d := (3 * U + 1) *
                                          (Finset.univ.filter (fun v : V =>
                                            MvPolynomial.eval v.val p = z.val)).card
                                        let b := π (MvPolynomial.C ((z.val - w)⁻¹)) *
                                          ∑ k ∈ Finset.range d,
                                            (-(π (MvPolynomial.C ((z.val - w)⁻¹)) *
                                              π (p - MvPolynomial.C z.val))) ^ k
                                        π (p - MvPolynomial.C w) * b = 1 ∧
                                          b * π (p - MvPolynomial.C w) = 1 ∧
                                          IsUnit (π (p - MvPolynomial.C w))) ∧
                                      ∀ q : Polynomial ℂ,
                                        let π := (Ideal.Quotient.mk
                                          (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))).comp
                                            (Ideal.Quotient.mk I)
                                        let d := (3 * U + 1) *
                                          (Finset.univ.filter (fun v : V =>
                                            MvPolynomial.eval v.val p = z.val)).card
                                        (q.eval₂ (π.comp MvPolynomial.C) (π p) -
                                          π (MvPolynomial.C (q.eval z.val))) ^ d = 0 ∧
                                        (IsUnit (q.eval₂ (π.comp MvPolynomial.C) (π p)) ↔
                                          q.eval z.val ≠ 0) ∧
                                        (IsNilpotent (q.eval₂ (π.comp MvPolynomial.C) (π p)) ↔
                                          q.eval z.val = 0))) ∧
                (let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
                 I ≤ R ∧
                 I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
                 FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
                 Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) +
                   Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree ∧
                 (∀ K : Ideal (MvPolynomial (Fin 4) ℂ), I ≤ K →
                   (J ≤ K ↔ I.colon (K : Set (MvPolynomial (Fin 4) ℂ)) ≤ R))) ∧
                (let p : ℕ → MvPolynomial (Fin 4) ℂ := fun j =>
                   (extensionChartDerivation L.g₂ L.g₃ c)^[j] (extensionChartNormalize c Q)
                 let T := (Finset.range s).filter (fun j =>
                   p j ∉ (I ⊔ Ideal.span (Set.range (fun i : Fin j => p i.val))))
                 J = I ⊔ Ideal.span (p '' (T : Set ℕ)) ∧
                 T.card + Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ M.natDegree ∧
                 (J = ⊤ → ∃ b : T → Polynomial ℂ,
                   (∀ j : T, (b j).degree < (M.natDegree : ℕ) ∧
                     (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (b j)).totalDegree ≤
                       M.natDegree - 1) ∧
                   1 - ∑ j : T,
                     Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * p j.val ∈ I ∧
                   ∀ D : ℕ, (∀ j : T, (p j.val).totalDegree ≤ D) →
                     (1 - ∑ j : T,
                       Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * p j.val).totalDegree ≤
                         M.natDegree - 1 + D)) ∧
                (∃ g : Polynomial ℂ,
                  g.Monic ∧ g ∣ M ∧ g.natDegree ≤ M.natDegree ∧
                  g = Nat.rec M (fun j h => gcd h
                    (MvPolynomial.aeval (Fin.cons Polynomial.X r)
                      ((extensionChartDerivation L.g₂ L.g₃ c)^[j]
                        (extensionChartNormalize c Q)))) s ∧
                  J = I ⊔ Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g} ∧
                  (let f : Fin 4 → MvPolynomial (Fin 4) ℂ :=
                     Fin.cons (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g)
                       (fun i : Fin 3 => MvPolynomial.X i.succ -
                         Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (r i))
                   J = Ideal.span (Set.range f) ∧
                   (∀ i : Fin 4, (f i).totalDegree ≤ max 1 M.natDegree) ∧
                   (∀ (k : ℕ) (i : Fin (k + 1) × Fin 4),
                     ((extensionChartDerivation L.g₂ L.g₃ c)^[i.1.val] (f i.2)).totalDegree ≤
                       max 1 M.natDegree + k)) ∧
                  (∀ f : MvPolynomial (Fin 4) ℂ,
                    f ∈ J ↔ g ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = g.natDegree ∧
                  (∀ p : MvPolynomial (Fin 4) ℂ,
                    let h := gcd g (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
                    let K := J ⊔ Ideal.span {p}
                    h.Monic ∧ h ∣ g ∧
                    (∀ f : MvPolynomial (Fin 4) ℂ,
                      f ∈ K ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
                    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
                    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = h.natDegree ∧
                    h.natDegree ≤ g.natDegree ∧
                    (h = g ↔ p ∈ J) ∧
                    (h.natDegree < g.natDegree ↔ p ∉ J) ∧
                    (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) <
                      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ↔ p ∉ J) ∧
                    (∀ q : Polynomial ℂ, q.Monic →
                      (∀ f : MvPolynomial (Fin 4) ℂ,
                        f ∈ K ↔ q ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → q = h)) ∧
                  (let δ := extensionChartDerivation L.g₂ L.g₃ c
                   let p := Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g
                   (∀ k : ℕ, δ^[k] p = Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
                     (Polynomial.derivative^[k] g)) ∧
                   δ^[g.natDegree] p = algebraMap ℂ (MvPolynomial (Fin 4) ℂ)
                     (g.natDegree.factorial : ℂ) ∧
                   (g.natDegree.factorial : ℂ)⁻¹ • δ^[g.natDegree] p = 1 ∧
                   (∀ k : ℕ, g.natDegree < k → δ^[k] p = 0) ∧
                   (∀ k : ℕ, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ k →
                     Ideal.span (Set.range (fun i : Fin (k + 1) => δ^[i.val] p)) = ⊤)) ∧
                  (∀ e : V → ℕ,
                    J = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v)) →
                    g = (∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ e v) ∧
                      ∀ z : ℂ, g.eval z = 0 ↔ ∃ v : V, 0 < e v ∧ z = v.val 0) ∧
                  (∀ h : Polynomial ℂ, h.Monic →
                    (∀ f : MvPolynomial (Fin 4) ℂ,
                      f ∈ J ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → h = g)) ∧
                FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
                (J ≠ ⊤ → ∃ p : MvPolynomial (Fin 4) ℂ,
                  p ∈ J ∧ extensionChartDerivation L.g₂ L.g₃ c p ∉ J) ∧
                (J ≠ ⊤ → ∃ g : Polynomial ℂ,
                  g.Monic ∧ 0 < g.natDegree ∧
                  g.natDegree ≤ Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
                  (∀ q : Polynomial ℂ, Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) q ∈ J ↔ g ∣ q) ∧
                  Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g ∈ J ∧
                  extensionChartDerivation L.g₂ L.g₃ c (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g) =
                    Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g.derivative ∧
                  g.derivative.natDegree < g.natDegree ∧
                  extensionChartDerivation L.g₂ L.g₃ c (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g) ∉ J) ∧
                ∃ e : V → ℕ,
                  (∀ v : V, e v ≤ 3 * U + 1 ∧ ∀ k ≤ 3 * U + 1,
                    k ≤ e v ↔ ∀ i : Fin s, ∀ j < k,
                      MvPolynomial.eval v.val
                        ((extensionChartDerivation L.g₂ L.g₃ c)^[j + i.val]
                          (extensionChartNormalize c Q)) = 0) ∧
                  J = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v)) ∧
                  (∀ (r₀ : ℕ) (f : Fin r₀ → MvPolynomial (Fin 4) ℂ),
                    J = Ideal.span (Set.range f) → ∀ k : ℕ,
                    let K := Ideal.span (Set.range (fun i : Fin (k + 1) × Fin r₀ =>
                      (extensionChartDerivation L.g₂ L.g₃ c)^[i.1.val] (f i.2)))
                    K = J ⊔ Ideal.span ((extensionChartDerivation L.g₂ L.g₃ c)^[k] ''
                      (J : Set (MvPolynomial (Fin 4) ℂ))) ∧
                      K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v - k)) ∧
                      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
                      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, (e v - k) ∧
                      (∀ p : MvPolynomial (Fin 4) ℂ,
                        p ∈ K ↔ ∃ q : MvPolynomial (Fin 4) ℂ, q ∈ J ∧
                          p - (extensionChartDerivation L.g₂ L.g₃ c)^[k] q ∈ J) ∧
                      (K = ⊤ ↔ ∀ v : V, e v ≤ k) ∧
                      (let K' := Ideal.span (Set.range
                         (fun i : Fin (k + 1 + 1) × Fin r₀ =>
                           (extensionChartDerivation L.g₂ L.g₃ c)^[i.1.val] (f i.2)))
                       K ≤ K' ∧
                       (K = K' ↔ K = ⊤) ∧
                       (K < K' ↔ ∃ v : V, k < e v) ∧
                       Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) =
                         Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K') +
                           (Finset.univ.filter (fun v : V => k < e v)).card)) ∧
                  (∀ k : ℕ,
                    let K := J ⊔ Ideal.span ((extensionChartDerivation L.g₂ L.g₃ c)^[k] ''
                      (J : Set (MvPolynomial (Fin 4) ℂ)))
                    K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v - k)) ∧
                      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
                      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, (e v - k) ∧
                      (∀ p : MvPolynomial (Fin 4) ℂ,
                        p ∈ K ↔ ∃ q : MvPolynomial (Fin 4) ℂ, q ∈ J ∧
                          p - (extensionChartDerivation L.g₂ L.g₃ c)^[k] q ∈ J) ∧
                      (K = ⊤ ↔ ∀ v : V, e v ≤ k)) ∧
                  (∀ f : V → ℕ,
                    let K : Ideal (MvPolynomial (Fin 4) ℂ) :=
                      ⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (f v)
                    (J ≤ K ↔ ∀ v : V, f v ≤ e v) ∧
                    (J = K ↔ e = f) ∧
                    (J < K ↔ (∀ v : V, f v ≤ e v) ∧ ∃ v : V, f v < e v)) ∧
                  Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
                    ((v : V) → Polynomial ℂ ⧸
                      Ideal.span {(Polynomial.X - Polynomial.C (v.val 0)) ^ e v})) ∧
                  J.radical = (⨅ v : V, if e v = 0 then ⊤ else RingHom.ker (MvPolynomial.eval v.val)) ∧
                  (∀ P' : Ideal (MvPolynomial (Fin 4) ℂ), P'.IsPrime →
                    (J ≤ P' ↔ ∃! v : V, 0 < e v ∧ P' = RingHom.ker (MvPolynomial.eval v.val))) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ v : V, e v ∧
                  I.colon (J : Set (MvPolynomial (Fin 4) ℂ)) =
                    (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (3 * U + 1 - e v)) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
                    I.colon (J : Set (MvPolynomial (Fin 4) ℂ))) =
                    ∑ v : V, (3 * U + 1 - e v) ∧
                  (let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
                   J ⊔ R = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val
                     (min (e v) (3 * U + 1 - e v))) ∧
                   FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) ∧
                   Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) =
                     ∑ v : V, min (e v) (3 * U + 1 - e v) ∧
                   (J ⊔ R = ⊤ ↔ ∀ v : V, e v = 0 ∨ e v = 3 * U + 1) ∧
                   ((∀ v : V, e v = 0 ∨ e v = 3 * U + 1) →
                     J ⊓ R = I ∧ J * R = I ∧
                     Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ]
                       (MvPolynomial (Fin 4) ℂ ⧸ J) × (MvPolynomial (Fin 4) ℂ ⧸ R)) ∧
                     ∃ p : MvPolynomial (Fin 4) ℂ,
                       p ∈ J ∧ 1 - p ∈ R ∧ p * p - p ∈ I ∧
                       J = I ⊔ Ideal.span {p} ∧ R = I ⊔ Ideal.span {1 - p}) ∧
                   (let K := J ⊓ R
                    I ≤ K ∧ K ^ 2 ≤ I ∧
                    K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val
                      (max (e v) (3 * U + 1 - e v))) ∧
                    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
                    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) =
                      ∑ v : V, max (e v) (3 * U + 1 - e v) ∧
                    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) +
                      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) =
                      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) ∧
                    (K = I ↔ J ⊔ R = ⊤))) ∧
                  (∀ p : MvPolynomial (Fin 4) ℂ,
                    let K := J.colon {p ^ (3 * U + 1)}
                    let e' : V → ℕ := fun v => if MvPolynomial.eval v.val p = 0 then 0 else e v
                    K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e' v)) ∧
                    (∀ q : MvPolynomial (Fin 4) ℂ, (∃ r : ℕ, q * p ^ r ∈ J) ↔ q ∈ K) ∧
                    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
                    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, e' v)) ∧
              (∃ b : Fin (B (m + 2 * n)) → Polynomial ℂ,
                (∀ k : Fin (B (m + 2 * n)),
                  (b k).degree < ((3 * U + 1) * Z.card : ℕ) ∧
                  (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (b k)).totalDegree ≤
                    (3 * U + 1) * Z.card - 1) ∧
                (1 - ∑ k : Fin (B (m + 2 * n)),
                  Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b k) *
                    ((extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q))) ∈ I ∧
                (1 - ∑ k : Fin (B (m + 2 * n)),
                  Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b k) *
                    ((extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q))).totalDegree ≤
                  ((3 * U + 1) * Z.card - 1) + (m + 2 * n + (B (m + 2 * n) - 1))) ∧
              ∀ p : MvPolynomial (Fin 4) ℂ,
                let q := MvPolynomial.aeval (Fin.cons Polynomial.X r) p
                let J := I ⊔ Ideal.span {p}
                Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
                  (Polynomial ℂ ⧸ Ideal.span {gcd M q})) ∧
                FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
                Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = (gcd M q).natDegree ∧
                Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ M.natDegree ∧
                (q ≠ 0 → Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ q.natDegree) ∧
                (let R := I.colon {p}
                 let G := M / gcd M q
                 (∀ f : MvPolynomial (Fin 4) ℂ,
                   f ∈ R ↔ G ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
                 Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ R) ≃ₐ[ℂ]
                   (Polynomial ℂ ⧸ Ideal.span {G})) ∧
                 FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
                 Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) = G.natDegree ∧
                 Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) +
                   Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree ∧
                 I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
                 I.colon (J : Set (MvPolynomial (Fin 4) ℂ)) = R) ∧
                ∃ e : V → ℕ,
                  (∀ v : V, e v ≤ 3 * U + 1 ∧ ∀ k ≤ 3 * U + 1,
                    k ≤ e v ↔ ∀ j < k,
                      MvPolynomial.eval v.val
                        ((extensionChartDerivation L.g₂ L.g₃ c)^[j] p) = 0) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ v : V, e v ∧
                  I.colon {p} =
                    (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (3 * U + 1 - e v)) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I.colon {p}) =
                    ∑ v : V, (3 * U + 1 - e v)) →
        ∃ H : Submodule ℤ (GraphExtensionGroup L.lattice η), ∃ a b : ℕ,
          ((a = 1 ∧ H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η)) ∨
            (a = 0 ∧ H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η))) ∧
          b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) *
            (H.mkQ '' (extensionCurve L.lattice η '' (X : Set ℂ))).ncard ≤
            C * (m : ℝ) ^ a * (n : ℝ) ^ b := by sorry
