-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_split_residual_multiplicity_obstruction
-- name    : WeierstrassEllipticZeta.split_residual_multiplicity_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-09T14:11:52.448096+00:00
-- url     : https://prove2.me/theorems/75bb6f79-40dd-4760-9fb8-1658c19714c4
-- title:
--   Multiplicity obstruction with product splittings for disjoint residual support
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
--   The factor $|Z_c|$ counts the actual complex points in that chart: the first coordinate of $f_c(z)$ is $z$, so $f_c$ is injective. Empty chart sets are allowed. Under these hypotheses,
--
--   there are an additive subgroup $H\subseteq G_\eta$ and nonnegative integers $a,b$ with $b\le2$, such that either $a=1$ and $H\subseteq\ker p_a$, or $a=0$ and $H\subseteq\ker p_E$, and
--
--   $$(U+1)|q_H(\varphi(X))|\le Cm^an^b.$$
--
--   Here $p_a(t,[(z,u)])=t$, $p_E(t,[(z,u)])=z\bmod\Lambda$, and $q_H$ is the additive quotient map. The triple-sumset vanishing is expressed as membership in an intersection of contact ideals, together with its exact complex quotient dimension. The map takes values in the part of the explicit projective algebraic locus covered by the two standard affine charts with coordinate indices zero and two. The explicit additive action and its fibers are supplied, and the parametrization is bijective and equivariant, and its derivatives are supplied in both projective charts. Identification with an algebraic-group embedding, the geometric multiplicity bound and subgroup projection profiles remain open obligations. The supplied bijection is between the underlying sets; topological and algebraic compatibility remain to be proved. No finiteness of subgroup intersections is assumed.
-- source:
--   Inferred specialization of Senthil Kumar K (2026), Appendix A.2, Theorem A.2 and Lemma A.1(b), https://doi.org/10.1017/S001309152610145X. At derivative-prefix stages whose contact orders are all zero or the full order, adds intersection and product identities, a quotient-algebra product decomposition and complementary idempotent generators modulo the original ideal. The existing comaximality criterion supplies precisely this conditional application. Every earlier binder, premise, witness, cutoff, coefficient bound, certificate, contact and intersection length, jet profile, stopping criterion, ideal decomposition, algebra model, radical, prime support, saturation result, canonical generator, time presentation, residual algebra and length balance, complementary contact orders, residual involution, inclusion equivalence and overlap data is retained, as are the positive-constant quantifier order, subgroup alternatives and final inequality. Global quantitative geometry, algebraic-group compatibility and subgroup profiles remain Open.

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

theorem WeierstrassEllipticZeta.split_residual_multiplicity_obstruction
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
                (let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
                 I ≤ R ∧
                 I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
                 FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
                 Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) +
                   Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree ∧
                 (∀ K : Ideal (MvPolynomial (Fin 4) ℂ), I ≤ K →
                   (J ≤ K ↔ I.colon (K : Set (MvPolynomial (Fin 4) ℂ)) ≤ R))) ∧
                (∃ g : Polynomial ℂ,
                  g.Monic ∧ g ∣ M ∧ g.natDegree ≤ M.natDegree ∧
                  J = I ⊔ Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g} ∧
                  (∀ f : MvPolynomial (Fin 4) ℂ,
                    f ∈ J ↔ g ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = g.natDegree ∧
                  (∀ h : Polynomial ℂ, h.Monic →
                    (∀ f : MvPolynomial (Fin 4) ℂ,
                      f ∈ J ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → h = g)) ∧
                FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
                ∃ e : V → ℕ,
                  (∀ v : V, e v ≤ 3 * U + 1 ∧ ∀ k ≤ 3 * U + 1,
                    k ≤ e v ↔ ∀ i : Fin s, ∀ j < k,
                      MvPolynomial.eval v.val
                        ((extensionChartDerivation L.g₂ L.g₃ c)^[j + i.val]
                          (extensionChartNormalize c Q)) = 0) ∧
                  J = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v)) ∧
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
                       J = I ⊔ Ideal.span {p} ∧ R = I ⊔ Ideal.span {1 - p})) ∧
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
