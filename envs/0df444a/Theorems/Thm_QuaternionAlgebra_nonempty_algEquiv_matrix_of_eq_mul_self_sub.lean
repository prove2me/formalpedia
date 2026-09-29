-- Prove2me | Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_eq_mul_self_sub
-- name    : QuaternionAlgebra.nonempty_algEquiv_matrix_of_eq_mul_self_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/42a2c1fd-d58b-5574-83a8-19a5836b6cc7
-- title:
--   Quaternion algebra splits when b=u²-av²
-- statement:
--   Let $F$ be a field in which $2 \neq 0$, let $a, b \in F$ with $a \neq 0$ and $b \neq 0$, and let $u, v \in F$ satisfy $b = u\cdot u - a\cdot(v \cdot v)$, i.e. $b$ is the value at $(u,v)$ of the norm form of $F[\sqrt{a}]$. The assertion is that the type of $F$-algebra isomorphisms from `QuaternionAlgebra F a 0 b` to the algebra $M_2(F)$ of $2\times 2$ matrices indexed by `Fin 2` is nonempty; here `QuaternionAlgebra F a 0 b` is the $F$-algebra with basis $1, i, j, k$ and relations $i^2 = a$, $j^2 = b$, $ij = k = -ji$, that is, the usual quaternion algebra $(a,b)_F$. Thus the conclusion is that $(a,b)_F$ splits, stated in the propositional form 'there exists an isomorphism' rather than by exhibiting a distinguished one.
--
--   This is the classical splitting criterion for quaternion algebras: $(a,b)_F$ is isomorphic to the matrix algebra as soon as $b$ is a norm from $F(\sqrt a)$, in the direction that is used to verify splitting at places. It is cited in the project by [`QuaternionAlgebra.nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit`](thm.html#QuaternionAlgebra.nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_eq_mul_self_sub.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem QuaternionAlgebra.nonempty_algEquiv_matrix_of_eq_mul_self_sub
    {F : Type*} [Field F] [NeZero (2 : F)] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    {u v : F} (huv : b = u * u - a * (v * v)) :
    Nonempty (QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by sorry
