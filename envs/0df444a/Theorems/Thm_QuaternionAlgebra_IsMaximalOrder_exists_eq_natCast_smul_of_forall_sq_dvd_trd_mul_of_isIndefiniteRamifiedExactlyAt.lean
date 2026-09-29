-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_forall_sq_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_forall_sq_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/4c1752b7-a189-5bcc-a9c4-4a6567182918
-- title:
--   Divisibility by r from r²-divisible traces against P
-- statement:
--   Let $a,b\in\mathbb Q$ and let $q,q'$ be primes, and suppose the quaternion algebra $B=\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb Q$ the completion $B\otimes_{\mathbb Q}\mathbb Q_v$ has all its nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb Z$-submodule which is a maximal order in the sense of the project: $\Lambda$ contains $1$, is closed under multiplication, spans $B$ over $\mathbb Q$ and is finitely generated, and every order containing $\Lambda$ equals $\Lambda$. Let $r$ be a natural number with $r=q$ or $r=q'$. Here $\operatorname{nrd}(x)=x_{\mathrm{re}}^2-a\,x_{\mathrm{imI}}^2-b\,x_{\mathrm{imJ}}^2+ab\,x_{\mathrm{imK}}^2$ and $\operatorname{trd}(x)=2x_{\mathrm{re}}$. The assertion is: for every $l\in\Lambda$, if for all $p\in\Lambda$ whose reduced norm is $r$ times an integer there exists an integer $t$ with $\operatorname{trd}(lp)=r^2t$, then $l=r\cdot l'$ for some $l'\in\Lambda$ (scalar multiplication by the integer $r$).
--
--   This is one half of the trace-duality statement at a ramified prime: the trace pairing $(l,p)\mapsto\operatorname{trd}(lp)/r$ on $\Lambda/\mathfrak P\times\mathfrak P/r\Lambda$ is non-degenerate in the first variable, $\mathfrak P$ being the unique two-sided ideal of $\Lambda$ above $r$. It feeds the characterisation of membership in the two-sided ideal by integrality of traces used in the local study of maximal and Eichler orders underlying the Čerednik–Drinfeld description of the associated Shimura curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_forall_sq_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_forall_sq_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q') :
    ∀ l ∈ Λ, (∀ p ∈ Λ, (∃ n : ℤ, nrd p = (r : ℚ) * n) → ∃ t : ℤ, trd (l * p) = ((r : ℚ) ^ 2) * t) →
      ∃ l' ∈ Λ, l = (r : ℤ) • l' := by sorry
