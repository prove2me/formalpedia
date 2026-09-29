-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_exists_submodule_forall_mem_iff_mul_eq_relIndex_eq_sq_of_nrd_eq
-- name    : QuaternionAlgebra.IsOrder.exists_submodule_forall_mem_iff_mul_eq_relIndex_eq_sq_of_nrd_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/70a6418c-4e4b-57cc-9f67-72d31040645d
-- title:
--   Index ℓ² of the left ideal Λ t when nrd(t)=ℓ
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense used here: $1\in\Lambda$, $\Lambda$ is closed under multiplication, the $\mathbb{Q}$-span of $\Lambda$ is all of $\mathbb{H}[\mathbb{Q},a,b]$, and $\Lambda$ is finitely generated as a $\mathbb{Z}$-module. Let $\ell$ be a natural number and let $t\in\Lambda$ satisfy $\mathrm{nrd}(t)=\ell$, where $\mathrm{nrd}(x)=x_{\mathrm{re}}^2-a\,x_{\mathrm{imI}}^2-b\,x_{\mathrm{imJ}}^2+ab\,x_{\mathrm{imK}}^2$. Then there is a $\mathbb{Z}$-submodule $J$ of $\mathbb{H}[\mathbb{Q},a,b]$ with the following five properties: an element $x$ lies in $J$ precisely when $x=yt$ for some $y\in\Lambda$, so that $J=\Lambda t$ as a set; $J\subseteq\Lambda$; for every $x\in\Lambda$ the element $\ell\cdot x$ (rational scalar multiplication by $\ell$) lies in $J$; $J$ is stable under left multiplication by elements of $\Lambda$; and the relative index of the additive subgroup underlying $J$ in the additive subgroup underlying $\Lambda$ equals $\ell^2$. Neither primality of $\ell$ nor maximality of $\Lambda$ is assumed.
--
--   This is the standard statement that for $t$ in an order $\Lambda$ of a rational quaternion algebra with reduced norm $\ell$, the principal left ideal $\Lambda t$ sits between $\ell\Lambda$ and $\Lambda$ and has index $\ell^{2}$; it packages the data of such an ideal in the form of an existential statement about a submodule $J$. It is used in the Čerednik–Drinfeld part of the development, in the construction of families with extra level structure where one must exhibit $\Lambda$-stable sublattices of index $\ell^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_exists_submodule_forall_mem_iff_mul_eq_relIndex_eq_sq_of_nrd_eq.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.exists_submodule_forall_mem_iff_mul_eq_relIndex_eq_sq_of_nrd_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ℓ : ℕ)
    (t : ℍ[ℚ, a, b]) (ht : t ∈ Λ) (hnrd : nrd t = (ℓ : ℚ)) :
    ∃ J : Submodule ℤ ℍ[ℚ, a, b],
      (∀ x : ℍ[ℚ, a, b], x ∈ J ↔ ∃ y ∈ Λ, y * t = x) ∧
      J ≤ Λ ∧ (∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ J) ∧
      (∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ J → (y : ℍ[ℚ, a, b]) * x ∈ J) ∧
      J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 := by sorry
