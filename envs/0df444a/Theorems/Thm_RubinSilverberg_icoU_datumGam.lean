-- Prove2me | Theorems.Thm_RubinSilverberg_icoU_datumGam
-- name    : RubinSilverberg.icoU_datumGam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/0578dc2d-3226-56a5-8e38-b30faad52d0d
-- title:
--   Equivariance of the form Γ₁₅ under Klein's half-turn
-- statement:
--   Let $K$ be a field of characteristic zero and let $\alpha,\beta,s,u \in K$ satisfy the four relations $\alpha\beta = -s$, $2\alpha^{2} = -5-s$, $2\beta^{2} = s-5$ and $s^{2} = 5$. Write $N = -\alpha u + \beta$ and $D = \beta u + \alpha$ for the two entries obtained by applying the matrix $\begin{pmatrix} -\alpha & \beta \\ \beta & \alpha\end{pmatrix}$ to $(u,1)$. The assertion is the polynomial identity
--   $$\bigl(N^{15} - 171\,N^{10}D^{5} + 247\,N^{5}D^{10} + 57\,D^{15}\bigr)\, N^{4} \;=\; s^{18}\Bigl(\beta\,(57u^{15} - 247u^{10} - 171u^{5} - 1) \;+\; \alpha\,u^{4}\,(u^{15} - 171u^{10} + 247u^{5} + 57)\Bigr)$$
--   in $K$. Thus the binary form $\Gamma_{15}(n,d) = n^{15} - 171 n^{10}d^{5} + 247 n^{5}d^{10} + 57 d^{15}$, evaluated at $(N,D)$ and multiplied by the extra factor $N^{4}$, is expressed as $s^{18}$ times an explicit $K$-linear combination, with coefficients $\beta$ and $\alpha$, of the degree-$15$ polynomial $57u^{15} - 247u^{10} - 171u^{5} - 1$ and of $u^{4}$ times $u^{15} - 171u^{10} + 247u^{5} + 57$. No non-degeneracy or non-vanishing hypothesis beyond the four relations is imposed.
--
--   The relations on $\alpha,\beta,s$ are those satisfied by $\zeta - \zeta^{4}$, $\zeta^{2} - \zeta^{3}$ and $\zeta + \zeta^{4} - \zeta^{2} - \zeta^{3} = \sqrt{5}$ for a primitive fifth root of unity $\zeta$, so that $s^{-1}\begin{pmatrix}-\alpha & \beta \\ \beta & \alpha\end{pmatrix}$ is Klein's half-turn generator $U$ of the binary icosahedral group; the identity is one row of the equivariance, under $U$, of the Möbius datum attached to the Rubin–Silverberg family of elliptic curves with constant mod-$5$ representation. It is used by [`RubinSilverberg.isIcoSymmetry_icoU`](thm.html#RubinSilverberg.isIcoSymmetry_icoU), the statement that $U$ is an icosahedral symmetry of that datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_icoU_datumGam.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.icoU_datumGam {K : Type*} [Field K] [CharZero K] (α β s u : K) (h1 : α * β = -s) (h2 : 2 * α ^ 2 = -5 - s) (h3 : 2 * β ^ 2 = s - 5) (h4 : s ^ 2 = 5) : ((-α * u + β) ^ 15 - 171 * (-α * u + β) ^ 10 * (β * u + α) ^ 5 + 247 * (-α * u + β) ^ 5 * (β * u + α) ^ 10 + 57 * (β * u + α) ^ 15) * (-α * u + β) ^ 4 = s ^ 18 * (β * (57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1) + α * (u ^ 4 * (u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57))) := by sorry
