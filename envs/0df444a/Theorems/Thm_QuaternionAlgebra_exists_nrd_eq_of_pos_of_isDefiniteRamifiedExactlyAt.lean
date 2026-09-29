-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/719f315a-b73b-50e6-a796-ed046a520801
-- title:
--   Hasse–Schilling norm theorem for a definite rational quaternion algebra
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q$ be a prime number, and suppose that the predicate [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q`](def/QuaternionAlgebra_EichlerOrder.html#L87) holds, i.e. $a<0$, $b<0$, and for every $v$ in the height-one spectrum of the ring of integers of $\mathbb{Q}$ the base change $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ to the $v$-adic completion has the property that every nonzero element is a unit precisely when $q$ lies in the prime ideal attached to $v$; thus $\mathbb{H}[\mathbb{Q},a,b]$ is definite and its completion is a division algebra exactly at the place above $q$. Then for every rational $t$ with $0<t$ there exists a quaternion $\gamma\in\mathbb{H}[\mathbb{Q},a,b]$ whose reduced norm, defined by $\operatorname{nrd}\gamma=\gamma_{\mathrm{re}}^2-a\,\gamma_{\mathrm{imI}}^2-b\,\gamma_{\mathrm{imJ}}^2+ab\,\gamma_{\mathrm{imK}}^2$, equals $t$. No restriction is placed on $q$; in particular the dyadic case $q=2$ is included. The conclusion asserts surjectivity of $\operatorname{nrd}$ onto the positive rationals as a map on all of the algebra, not on its unit group, although for $t>0$ the element produced is automatically invertible.
--
--   This is the norm theorem of Hasse–Schilling–Eichler in the case of a definite rational quaternion algebra ramified at a single finite prime: the image of the reduced norm is exactly the group of positive rationals, the positivity condition coming from the ramified real place. It is used in the Čerednik–Drinfel'd part of the development, through [`CerednikDrinfeld.CosetGraph.exists_mem_awayUnits_nrd_eq_of_le_isMaximalOrder`](thm.html#CerednikDrinfeld.CosetGraph.exists_mem_awayUnits_nrd_eq_of_le_isMaximalOrder), to produce elements of prescribed reduced norm in a maximal order away from $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt
    {a b : ℚ} {q : ℕ} [Fact q.Prime]
    (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    (t : ℚ) (ht : 0 < t) :
    ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = t := by sorry
