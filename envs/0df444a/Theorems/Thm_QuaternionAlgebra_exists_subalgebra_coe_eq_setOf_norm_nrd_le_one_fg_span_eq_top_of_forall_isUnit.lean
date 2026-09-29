-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_subalgebra_coe_eq_setOf_norm_nrd_le_one_fg_span_eq_top_of_forall_isUnit
-- name    : QuaternionAlgebra.exists_subalgebra_coe_eq_setOf_norm_nrd_le_one_fg_span_eq_top_of_forall_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/a0c18807-a1cf-5973-ac68-9ef99183e43a
-- title:
--   The reduced-norm unit ball is a ℤₚ-order
-- statement:
--   Let $p$ be a natural number that is prime, and let $a, b \in \mathbb{Q}_p$, so that $\mathbb{H}[\mathbb{Q}_p, a, b]$ is the quaternion algebra over $\mathbb{Q}_p$ with $i^2 = a$, $j^2 = b$. Assume that every nonzero element of $\mathbb{H}[\mathbb{Q}_p, a, b]$ is a unit, i.e. that this algebra is a division algebra. The assertion is that there exists a $\mathbb{Z}_p$-subalgebra $O$ of $\mathbb{H}[\mathbb{Q}_p, a, b]$ with the following three properties. First, the underlying set of $O$ is exactly the unit ball of the reduced norm, namely the set of $z$ with $\|\mathrm{nrd}\, z\| \le 1$, where [`QuaternionAlgebra.nrd`](def/QuaternionAlgebra_ReducedNorm.html#L11) is the quadratic form $\mathrm{nrd}\, z = z_{\mathrm{re}}^2 - a\, z_{i}^2 - b\, z_{j}^2 + ab\, z_{k}^2$ in the four coordinates of $z$, and $\|\cdot\|$ is the $p$-adic absolute value on $\mathbb{Q}_p$. Second, $O$, viewed as a $\mathbb{Z}_p$-submodule of $\mathbb{H}[\mathbb{Q}_p, a, b]$, is finitely generated. Third, the $\mathbb{Q}_p$-span of the set $O$ is the whole algebra. Thus the reduced-norm unit ball is a $\mathbb{Z}_p$-order in the division algebra.
--
--   This is the local statement that in a quaternion division algebra over $\mathbb{Q}_p$ the valuation ring $\{z : |\mathrm{nrd}\, z|_p \le 1\}$ is a $\mathbb{Z}_p$-order (in fact the unique maximal one). It feeds the description of local boxes at ramified places, being used by [`QuaternionAlgebra.IsMaximalOrder.exists_ringEquiv_coe_localBox_eq_setOf_norm_nrd_le_one_of_forall_isUnit`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_ringEquiv_coe_localBox_eq_setOf_norm_nrd_le_one_of_forall_isUnit), [`QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit`](thm.html#QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit) and [`QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit`](thm.html#QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit); the integrality of the reduced trace on the unit ball is supplied by [`QuaternionAlgebra.norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one`](thm.html#QuaternionAlgebra.norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_subalgebra_coe_eq_setOf_norm_nrd_le_one_fg_span_eq_top_of_forall_isUnit.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_subalgebra_coe_eq_setOf_norm_nrd_le_one_fg_span_eq_top_of_forall_isUnit
    (p : ℕ) [Fact p.Prime] (a b : ℚ_[p])
    (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x) :
    ∃ O : Subalgebra ℤ_[p] ℍ[ℚ_[p], a, b],
      (O : Set ℍ[ℚ_[p], a, b]) = {z | ‖QuaternionAlgebra.nrd z‖ ≤ 1} ∧
      (Subalgebra.toSubmodule O).FG ∧
      Submodule.span ℚ_[p] (O : Set ℍ[ℚ_[p], a, b]) = ⊤ := by sorry
