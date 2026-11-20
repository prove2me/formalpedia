-- Prove2me | Theorems.Thm_QuantumSixJ_sum_prefactor_match
-- name    : QuantumSixJ.sum_prefactor_match
-- status  : Proved
-- author  : @igor.kh
-- created : 2026-11-13T09:30:21.650063+00:00
-- url     : https://prove2.me/theorems/a5874918-18da-41cb-8928-6bc771285531
-- title:
--   Factorial-prefactor matching for the finite Tet sum
-- statement:
--   Let $a,b,c,d,j,l$ be integers satisfying horizontal and vertical admissibility, with $j>0$. Write $R$ for the three-term residual of the normalized Appendix Tet sum, $P$ for its Appendix factorial prefactor, $D_j=[2][j][j+1][j+2]$, and $\mathcal R$ for the sum of cleared raw neighboring residuals defined by the certificate bundle. Then
--   $$R=\frac{P}{D_j}\,\mathcal R.$$
--   This identity relates independently defined finite sums, including absent-neighbor cases; it does not assert that either residual vanishes.
--
--   ### Independent mathematical read-back
--
--   # Read-back: `QuantumSixJ.sum_prefactor_match`
--
--   For every six integers $a,b,c,d,j,l$, assume that each of the four triples $(a,d,j)$, $(b,c,j)$, $(a,b,l)$, $(c,d,l)$ consists of nonnegative integers, satisfies all three triangle inequalities, and has even total, and additionally assume $j>0$. The theorem asserts the rational-function identity
--   $$
--   m_-U_{j-2,l}+\big(m_0-E(a,b,l)N_j\big)U_{j,l}+m_+U_{j+2,l}
--   =\frac{P_{j,l}}{[2][j][j+1][j+2]}\sum_{S=0}^{n-1}R(S),
--   $$
--   with every quantity specified as follows within this paragraph. All scalars belong to $K=\mathbb Q(q)$, where $q$ is the image of the polynomial indeterminate, and $[u]=(q^u-q^{-u})/(q-q^{-1})$ for every integer $u$; write $F(u)=0$ for $u<0$ and $F(u)=\prod_{v=1}^{u}[v]$ otherwise, so $F(0)=1$. All inverses and divisions are total field operations, with $0^{-1}=0$ and $x/0=0$; integer powers are field powers, every label subtraction is integer subtraction, and every half-sum below uses Euclidean integer division by $2$. Let $T(u,v,w)$ denote exactly the nonnegativity, three triangle inequalities, and even-total condition just stated, and put $H_r=T(a,d,r)\land T(b,c,r)$ and $V_s=T(a,b,s)\land T(c,d,s)$. Define
--   $$
--   \delta(r)=\begin{cases}(-1)^r[r+1]&r\geq0,\\0&r<0,\end{cases}\qquad
--   \vartheta(u,v,w)=\begin{cases}
--   \displaystyle\frac{(-1)^zF(z+1)F(z-u)F(z-v)F(z-w)}{F(u)F(v)F(w)},\ z=(u+v+w)/2&T(u,v,w),\\0&\text{otherwise},
--   \end{cases}
--   $$
--   $$
--   N_r=\begin{cases}\vartheta(a,d,r)\vartheta(b,c,r)/\delta(r)&H_r,\\0&\text{otherwise},\end{cases}\qquad
--   E(u,v,w)=\begin{cases}
--   \displaystyle\frac{[(u-v+w)/2][(-u+v+w)/2]-[(u+v-w)/2][(u+v+w)/2+2]}{[2]}&T(u,v,w),\\0&\text{otherwise}.
--   \end{cases}
--   $$
--   The three coefficients on the left are exactly
--   $$
--   \begin{aligned}
--   m_-&=\begin{cases}N_j[(a+d-j+2)/2][(b+c-j+2)/2]&H_j\land H_{j-2},\\0&\text{otherwise},\end{cases}\\
--   m_0&=\begin{cases}-N_j[2]E(a,j,d)E(b,j,c)/([j][j+2])&H_j\land j\ne0,\\0&\text{otherwise},\end{cases}\\
--   m_+&=\begin{cases}N_{j+2}[(a+d-j)/2][(b+c-j)/2]&H_j\land H_{j+2},\\0&\text{otherwise}.\end{cases}
--   \end{aligned}
--   $$
--   For arbitrary integer channels $r,s$, use zero-based lists
--   $$
--   \alpha^{r,s}=\big((a+d+r)/2,(b+c+r)/2,(a+b+s)/2,(c+d+s)/2\big),\qquad
--   \beta^{r,s}=\big((b+d+r+s)/2,(a+c+r+s)/2,(a+b+c+d)/2\big),
--   $$
--   and set
--   $$
--   P_{r,s}=\frac{\prod_{i=0}^{3}\prod_{k=0}^{2}F(\beta_k^{r,s}-\alpha_i^{r,s})}{F(a)F(b)F(c)F(d)F(r)F(s)},\qquad
--   U_{r,s}=\frac{1}{N_r}\begin{cases}
--   \displaystyle P_{r,s}\sum_{z=0}^{a+b+c+d+r+s}
--   \frac{(-1)^zF(z+1)}{\big(\prod_{i=0}^{3}F(z-\alpha_i^{r,s})\big)\big(\prod_{k=0}^{2}F(\beta_k^{r,s}-z)\big)}&H_r\land V_s,\\0&\text{otherwise}.
--   \end{cases}
--   $$
--   An integer-indexed sum with upper endpoint below $0$ is empty and equals zero. For the right side of the asserted identity set
--   $$
--   A=(a+d+j)/2,\quad B=(b+c+j)/2,\quad C=(a+b+l)/2,\quad E=(b+d+j+l)/2,\quad F=(a+c+j+l)/2,
--   $$
--   $$
--   D=E+F-C-j,\qquad G=A+B-j,\qquad n=\max(a+b+c+d+j+l,0)+3.
--   $$
--   Here the bare symbol $F$ is an integer parameter and $F(\cdot)$ continues to mean the signed-index factorial; the maximum is converted to a natural number before adding $3$. Set
--   $$
--   \begin{aligned}
--   p_-&=[A-j+1][B-j+1][A+1][B+1][2][j+2],\\
--   p_0&=-\Big(([A-j][E-C]-[F-D][A+2])([B-j][F-C]-[E-D][B+2])\\
--   &\hspace{18mm}+([F-B][E-A]-[G-D][C+2])[j][j+2]\Big)[j+1],\\
--   p_+&=[E-C+1][F-D+1][F-C+1][E-D+1][2][j],
--   \end{aligned}
--   $$
--   and define the summand on the right by the fully specified three-term expression
--   $$
--   \begin{aligned}
--   R(S)={}&p_-\frac{(-1)^S F(S+1)}{F(S-A+1)F(S-B+1)F(S-C)F(S-D)F(E-1-S)F(F-1-S)F(G-S)}\\
--   &+p_0\frac{(-1)^S F(S+1)}{F(S-A)F(S-B)F(S-C)F(S-D)F(E-S)F(F-S)F(G-S)}\\
--   &+p_+\frac{(-1)^S F(S+1)}{F(S-A-1)F(S-B-1)F(S-C)F(S-D)F(E+1-S)F(F+1-S)F(G-S)}.
--   \end{aligned}
--   $$
--   The sum over $S$ consists of the natural numbers $0,\ldots,n-1$ cast to integers; the stated hypotheses imply that the total defining $n$ is positive, but the underlying length expression truncates a negative total to zero before adding $3$. There is no hypothesis that $j-2$ or $j+2$ is admissible, that either neighbor exists, or that any of the displayed summands or their denominator factorials are nonzero. In particular $j=1$ is included, with negative lower channel and hence $m_-=U_{j-2,l}=0$; inadmissible upper or lower channels use the displayed zero branches. The assumption $j>0$ excludes $j=0$, but permits the external labels or $l$ to be zero whenever the four triple conditions hold. No complex specialization, numerical parameter, typeclass assumption, or additional existentially chosen object is part of the statement.
-- source:
--   I. Khavkine, Recurrence relation for the 6j-symbol of su_q(2) as a symmetric eigenvalue problem, https://arxiv.org/abs/1009.2261, Appendix finite Tet formula and Eq. (24); auxiliary factorial-shift and telescoping-certificate calculation for those formulas.

import Definitions.Def_QuantumSixJSumCertificate

open scoped BigOperators QuantumSixJ
open QuantumSixJ.Certificate

namespace QuantumSixJ

theorem sum_prefactor_match (a b c d j l : ℤ)
    (hj : hAdmissible a b c d j) (hl : vAdmissible a b c d l) (hpos : 0 < j) :
    mainResidual a b c d j l =
      (prefactor a b c d j l / clearingFactor j) * totalResidual a b c d j l
 := by sorry

end QuantumSixJ
