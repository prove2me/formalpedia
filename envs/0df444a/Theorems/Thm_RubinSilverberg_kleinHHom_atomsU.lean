-- Prove2me | Theorems.Thm_RubinSilverberg_kleinHHom_atomsU
-- name    : RubinSilverberg.kleinHHom_atomsU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/27f7c715-b0c7-5aee-89d9-6bc26075e972
-- title:
--   Covariance of Klein's face form under the icosahedral half-turn
-- statement:
--   Let $K$ be a field of characteristic zero and let $\alpha,\beta,s,n,d$ be elements of $K$ satisfying the four relations $\alpha\beta=-s$, $2\alpha^{2}=-5-s$, $2\beta^{2}=s-5$ and $s^{2}=5$. Write $H$ for the binary form of degree $20$ given by $H(n,d)=n^{20}-228\,n^{15}d^{5}+494\,n^{10}d^{10}+228\,n^{5}d^{15}+d^{20}$, which is how `kleinHHom` is defined over any commutative ring. The assertion is the single polynomial identity
--   $$H(-\alpha n+\beta d,\ \beta n+\alpha d)=s^{20}\,H(n,d)$$
--   in $K$. Note that no invertibility is assumed of $s$, $\alpha$ or $\beta$, and the substitution is by the integral matrix $\begin{pmatrix}-\alpha&\beta\\ \beta&\alpha\end{pmatrix}$ rather than by its normalisation by $1/s$; the factor $s^{20}$ on the right is exactly the twentieth power of the corresponding scaling, so the statement is the covariance of weight $20$ in unnormalised form. Since $n$ and $d$ range over arbitrary elements of $K$, this is an identity of binary forms in the two variables, and the hypotheses on $\alpha,\beta,s$ are used only through the four stated relations.
--
--   Here $H$ is Klein's face form of the icosahedron, of degree $20$ in the homogeneous coordinates of the projective line, and the substitution is the half-turn generator $U$ of the binary icosahedral group written in terms of $\alpha=\zeta-\zeta^{4}$, $\beta=\zeta^{2}-\zeta^{3}$ and $s=\sqrt 5$ for a primitive fifth root of unity $\zeta$; stating it over an abstract base field with the four relations as hypotheses turns the covariance into a finite polynomial identity. It feeds the verification [`RubinSilverberg.isIcoSymmetry_icoU`](thm.html#RubinSilverberg.isIcoSymmetry_icoU) that $U$ is an icosahedral symmetry of the Rubin–Silverberg datum, used in the construction of families of elliptic curves with constant mod $5$ representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_kleinHHom_atomsU.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.kleinHHom_atomsU {K : Type*} [Field K] [CharZero K] (α β s n d : K) (h1 : α * β = -s) (h2 : 2 * α ^ 2 = -5 - s) (h3 : 2 * β ^ 2 = s - 5) (h4 : s ^ 2 = 5) : kleinHHom (-α * n + β * d) (β * n + α * d) = s ^ 20 * kleinHHom n d := by sorry
