-- Prove2me | Theorems.Thm_RubinSilverberg_kleinVHom_one_right
-- name    : RubinSilverberg.kleinVHom_one_right
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/d9ecc31e-a51e-5074-a888-0221cbf7ea8d
-- title:
--   Dehomogenising Klein's vertex form: V(n,1)=V(n)
-- statement:
--   Let $R$ be a commutative ring (the type is arbitrary, with the commutative ring structure supplied as a typeclass assumption) and let $n \in R$. The project's two-variable polynomial `kleinVHom` is defined by $\mathtt{kleinVHom}(n,d) = n\,d\,(n^{10} + 11 n^{5} d^{5} - d^{10})$, a homogeneous form of degree $12$ in $(n,d)$, and the one-variable polynomial `kleinV` is defined by $\mathtt{kleinV}(u) = u\,(u^{10} + 11 u^{5} - 1)$. The theorem asserts the identity obtained by substituting $d = 1$: $\mathtt{kleinVHom}(n,1) = \mathtt{kleinV}(n)$ in $R$, for every $n$. No invertibility, characteristic or non-degeneracy assumption on $R$ or on $n$ is imposed; the statement is the literal equality of the two ring elements $n \cdot 1 \cdot (n^{10} + 11 n^{5} \cdot 1^{5} - 1^{10})$ and $n\,(n^{10} + 11 n^{5} - 1)$.
--
--   The two polynomials are Klein's vertex form for the icosahedron in its homogeneous (degree $12$) and affine shapes, the latter in the coordinate on the modular curve of level $5$; the identity is the passage to the affine chart $d = 1$. It serves as bookkeeping in the construction of the Rubin–Silverberg family of elliptic curves with prescribed mod $5$ representation, and is used in the proof of [`RubinSilverberg.exists_torsionBy_linearEquiv_rsMember`](thm.html#RubinSilverberg.exists_torsionBy_linearEquiv_rsMember).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_kleinVHom_one_right.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.kleinVHom_one_right {R : Type*} [CommRing R] (n : R) : kleinVHom n 1 = kleinV n := by sorry
