-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_exists_forall_exists_units_smul_conj_mem_of_int_trd_nrd
-- name    : QuaternionAlgebra.IsOrder.exists_forall_exists_units_smul_conj_mem_of_int_trd_nrd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/5aff5f7f-5410-52e4-af7d-8643d690b4a4
-- title:
--   Uniform denominator for integral quaternions up to conjugacy
-- statement:
--   Let $a,b\in\mathbb{Q}$ with $a<0$ and $b<0$, and let $\mathbb{H}=\mathbb{H}[\mathbb{Q},a,b]$ be the associated rational quaternion algebra. Let $O\subseteq\mathbb{H}$ be a $\mathbb{Z}$-submodule satisfying [`QuaternionAlgebra.IsOrder`](def/QuaternionAlgebra_Order.html#L11), that is: $1\in O$; $xy\in O$ whenever $x,y\in O$; the $\mathbb{Q}$-span of $O$ is all of $\mathbb{H}$; and $O$ is finitely generated as a $\mathbb{Z}$-module. The assertion is that there exists a natural number $d\neq 0$ with the following property: for every $\alpha\in\mathbb{H}$ whose reduced trace $\operatorname{trd}(\alpha)=2\alpha_{\mathrm{re}}$ and reduced norm $\operatorname{nrd}(\alpha)=\alpha_{\mathrm{re}}^2-a\,\alpha_{I}^2-b\,\alpha_{J}^2+ab\,\alpha_{K}^2$ both lie in the image of $\mathbb{Z}$ in $\mathbb{Q}$ (i.e. there are $t,n\in\mathbb{Z}$ with $\operatorname{trd}(\alpha)=t$ and $\operatorname{nrd}(\alpha)=n$), there is a unit $\mu\in\mathbb{H}^{\times}$ such that $d\cdot(\mu\alpha\mu^{-1})\in O$. The integer $d$ is uniform: it is chosen before $\alpha$ and depends only on $a$, $b$ and $O$.
--
--   This is the uniform-denominator statement that every integral element of a definite rational quaternion algebra (one satisfying a monic integral quadratic equation) can be conjugated into the fixed lattice $d^{-1}O$ attached to a given order $O$, a finiteness consequence of the pigeonhole argument underlying the Jordan–Zassenhaus theorem. It is used in the construction of elements of reduced norm one with prescribed congruence behaviour, namely by [`QuaternionAlgebra.IsOrder.exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul`](thm.html#QuaternionAlgebra.IsOrder.exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul), which feeds into strong approximation for the norm-one group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_exists_forall_exists_units_smul_conj_mem_of_int_trd_nrd.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.exists_forall_exists_units_smul_conj_mem_of_int_trd_nrd
    {a b : ℚ} (ha : a < 0) (hb : b < 0)
    {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ α : ℍ[ℚ, a, b],
      (∃ t n : ℤ, QuaternionAlgebra.trd α = t ∧ QuaternionAlgebra.nrd α = n) →
      ∃ μ : (ℍ[ℚ, a, b])ˣ, (d : ℚ) • ((μ : ℍ[ℚ, a, b]) * α * ↑μ⁻¹) ∈ O := by sorry
