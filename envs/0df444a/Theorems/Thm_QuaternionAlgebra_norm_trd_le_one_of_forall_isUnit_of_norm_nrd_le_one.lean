-- Prove2me | Theorems.Thm_QuaternionAlgebra_norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one
-- name    : QuaternionAlgebra.norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/6c29da29-fe23-5375-b5ab-e1184fc97421
-- title:
--   Reduced trace is integral when the reduced norm is, in a p-adic division quaternion algebra
-- statement:
--   Let $p$ be a prime and let $a,b \in \mathbb{Q}_p$, and consider the quaternion algebra $\mathbb{H}[\mathbb{Q}_p,a,b]$ over $\mathbb{Q}_p$ with generators $i,j$ satisfying $i^2=a$, $j^2=b$, $ij=-ji=k$. Assume that every nonzero element of $\mathbb{H}[\mathbb{Q}_p,a,b]$ is a unit, i.e. that the algebra is a division algebra. Let $z$ be an element of $\mathbb{H}[\mathbb{Q}_p,a,b]$, with components $z_{\mathrm{re}}, z_{\mathrm{imI}}, z_{\mathrm{imJ}}, z_{\mathrm{imK}}$, and suppose that its reduced norm $\mathrm{nrd}(z) = z_{\mathrm{re}}^2 - a\,z_{\mathrm{imI}}^2 - b\,z_{\mathrm{imJ}}^2 + ab\,z_{\mathrm{imK}}^2$ satisfies $\lVert \mathrm{nrd}(z)\rVert \le 1$ for the $p$-adic absolute value. The conclusion is that the reduced trace $\mathrm{trd}(z) = 2 z_{\mathrm{re}}$ likewise satisfies $\lVert \mathrm{trd}(z)\rVert \le 1$. Here $\mathrm{nrd}$ and $\mathrm{trd}$ are the polynomial expressions just displayed, defined for quaternion algebras over any commutative ring.
--
--   This is the integrality half of the statement that, in a quaternion division algebra over $\mathbb{Q}_p$, the set of elements of reduced norm of absolute value at most $1$ is the valuation ring: it is the Newton-polygon argument for the characteristic polynomial $X^2 - \mathrm{trd}(z)X + \mathrm{nrd}(z)$. It is used to show that this set is closed under addition and forms a subalgebra which is finitely generated and spans, in the local analysis of the quaternion algebra at a ramified prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one
    (p : ℕ) [Fact p.Prime] (a b : ℚ_[p])
    (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x)
    (z : ℍ[ℚ_[p], a, b]) (hz : ‖QuaternionAlgebra.nrd z‖ ≤ 1) :
    ‖QuaternionAlgebra.trd z‖ ≤ 1 := by sorry
