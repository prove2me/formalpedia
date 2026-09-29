-- Prove2me | Theorems.Thm_RubinSilverberg_kleinVHom_atomsU
-- name    : RubinSilverberg.kleinVHom_atomsU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/f59c3ec8-d7fb-5465-b374-e50cf2986a3b
-- title:
--   Klein's vertex form is a weight-12 relative invariant under U
-- statement:
--   Let $K$ be a field of characteristic zero and let $\alpha,\beta,s,n,d$ be elements of $K$ satisfying the four relations $\alpha\beta=-s$, $2\alpha^{2}=-5-s$, $2\beta^{2}=s-5$ and $s^{2}=5$. Write $\mathrm{kleinVHom}(x,y)=xy\,(x^{10}+11x^{5}y^{5}-y^{10})$ for the degree-$12$ binary form in two ring elements defined in the project. The assertion is the polynomial identity $$\mathrm{kleinVHom}(-\alpha n+\beta d,\ \beta n+\alpha d)=s^{12}\,\mathrm{kleinVHom}(n,d)$$ in $K$. Thus substituting the pair $(n,d)$ by its image under the matrix $\begin{pmatrix}-\alpha&\beta\\ \beta&\alpha\end{pmatrix}$ multiplies the form by $s^{12}=5^{6}$; equivalently, after dividing the matrix by $s$ to normalise its determinant, the form is invariant. The statement is made for arbitrary elements subject to the four displayed relations, with no root of unity or algebraic number field mentioned, so it is a purely algebraic identity valid in any characteristic-zero field containing such a configuration.
--
--   The form $\mathrm{kleinVHom}$ is Klein's binary icosahedral form of degree $12$ whose roots are the vertices of the icosahedron, and the substitution here is the half-turn generator of the binary icosahedral group in $\mathrm{SL}_2$ over $\mathbb{Q}(\sqrt5)$, realised by $\alpha=\zeta-\zeta^{4}$, $\beta=\zeta^{2}-\zeta^{3}$, $s=\sqrt5$ for $\zeta$ a primitive fifth root of unity. It is one of the invariance identities used by [`RubinSilverberg.isIcoSymmetry_icoU`](thm.html#RubinSilverberg.isIcoSymmetry_icoU), in the treatment of the Rubin–Silverberg family of elliptic curves with constant mod-$5$ representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_kleinVHom_atomsU.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.kleinVHom_atomsU {K : Type*} [Field K] [CharZero K] (α β s n d : K) (h1 : α * β = -s) (h2 : 2 * α ^ 2 = -5 - s) (h3 : 2 * β ^ 2 = s - 5) (h4 : s ^ 2 = 5) : kleinVHom (-α * n + β * d) (β * n + α * d) = s ^ 12 * kleinVHom n d := by sorry
