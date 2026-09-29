-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_exists_mem_dvd_nrd_forall_ne_smul
-- name    : QuaternionAlgebra.IsOrder.exists_mem_dvd_nrd_forall_ne_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/f2491267-bbc5-53c5-b17e-795fbc382831
-- title:
--   Reduced norm of an order has a nontrivial zero mod p
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\mathbb{H}[\mathbb{Q},a,b]$ be the associated quaternion algebra over $\mathbb{Q}$, with reduced norm $\mathrm{nrd}(x)=x_{\mathrm{re}}^2-a\,x_{\mathrm{imI}}^2-b\,x_{\mathrm{imJ}}^2+ab\,x_{\mathrm{imK}}^2$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ satisfying [`QuaternionAlgebra.IsOrder`](def/QuaternionAlgebra_Order.html#L11), that is: $1\in\Lambda$; $\Lambda$ is closed under multiplication ($x,y\in\Lambda$ implies $xy\in\Lambda$); the $\mathbb{Q}$-span of $\Lambda$ is all of $\mathbb{H}[\mathbb{Q},a,b]$; and $\Lambda$ is finitely generated as a $\mathbb{Z}$-module. Let $p$ be a prime number. The assertion is that there exists $h\in\Lambda$ with the following two properties: first, $h$ is not divisible by $p$ inside $\Lambda$, i.e. $h\neq p\cdot h'$ for every $h'\in\Lambda$ (in particular $h\neq 0$, since $0=p\cdot 0$); second, there is an integer $n$ whose image in $\mathbb{Q}$ equals $\mathrm{nrd}(h)$ and which is divisible by $p$ in $\mathbb{Z}$. Thus the quaternary quadratic form $\mathrm{nrd}$ restricted to the lattice $\Lambda$, which takes integer values, has a zero modulo $p$ that is nontrivial modulo $p\Lambda$.
--
--   This is the Chevalley–Warning input for the local study of orders in rational quaternion algebras: the integral quaternary form $\mathrm{nrd}|_\Lambda$ is isotropic modulo every prime. It is used in the analysis of maximal orders ramified at prescribed places, for instance in [`QuaternionAlgebra.IsMaximalOrder.exists_mem_dvd_nrd_not_sq_dvd_nrd_of_isIndefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_mem_dvd_nrd_not_sq_dvd_nrd_of_isIndefiniteRamifiedExactlyAt) and [`QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_isIndefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_isIndefiniteRamifiedExactlyAt), and further downstream in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_exists_mem_dvd_nrd_forall_ne_smul.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.exists_mem_dvd_nrd_forall_ne_smul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (p : ℕ) [Fact p.Prime] :
    ∃ h ∈ Λ, (∀ h' ∈ Λ, h ≠ (p : ℤ) • h') ∧
      ∃ n : ℤ, (n : ℚ) = QuaternionAlgebra.nrd h ∧ (p : ℤ) ∣ n := by sorry
