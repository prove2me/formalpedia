-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_forall_exists_smul_add_mul_iff_mul_of_isUnitOf_right
-- name    : QuaternionAlgebra.IsOrder.forall_exists_smul_add_mul_iff_mul_of_isUnitOf_right
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/ec17f381-5010-5de6-a614-c1fc10f1e3c6
-- title:
--   Right translation by a unit preserves the level identity
-- statement:
--   Fix rationals $a,b$ and a natural number $N$, and work in the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$. Let $\Lambda, R, J'$ be $\mathbb{Z}$-submodules of $\mathbb{H}[\mathbb{Q},a,b]$ such that $R$ satisfies `IsOrder`, i.e. $1 \in R$, $R$ is closed under multiplication, the $\mathbb{Q}$-span of $R$ is all of $\mathbb{H}[\mathbb{Q},a,b]$, and $R$ is finitely generated over $\mathbb{Z}$; assume $R \le \Lambda$, and assume the level block: $\Lambda \le J'$, $x y \in J'$ for all $x \in \Lambda$, $y \in J'$, $N y \in \Lambda$ for all $y \in J'$, the relative index of $J'$ in $\Lambda$ as additive subgroups equals $N^2$, and for $x \in \Lambda$ one has $x \in R$ if and only if $y x \in J'$ for all $y \in J'$. Let $\ell \in \mathbb{N}$ and $t, v \in R$, with $v$ possessing a two-sided inverse $v' \in R$. Assume the level identity for $t$: for every $x$, $x$ is of the form $\ell j + m t$ with $j \in J'$, $m \in \Lambda$ if and only if $x = j t$ for some $j \in J'$. The conclusion is threefold: $t v \in R$; $\mathrm{nrd}(tv) = \mathrm{nrd}(t)\,\mathrm{nrd}(v)$, where $\mathrm{nrd}(x) = x_{\mathrm{re}}^2 - a\,x_{\mathrm{imI}}^2 - b\,x_{\mathrm{imJ}}^2 + ab\,x_{\mathrm{imK}}^2$; and the same level identity holds with $t$ replaced by $tv$.
--
--   Elementwise form of the stability of the level identity $\ell J' + \Lambda t = J' t$ under right translation of $t$ by a unit of the order $R$, together with multiplicativity of the reduced norm, in the setting of an Eichler-type pair $(\Lambda, J')$ with $R = \{x \in \Lambda : J' x \subseteq J'\}$. It is used in the Čerednik–Drinfeld part of the development, in the fine-moduli statement about analytic families with extra level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_forall_exists_smul_add_mul_iff_mul_of_isUnitOf_right.lean

import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.forall_exists_smul_add_mul_iff_mul_of_isUnitOf_right
    {a b : ℚ} {N : ℕ} (Λ R J' : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (hRΛ : R ≤ Λ)
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (t v : ℍ[ℚ, a, b]) (ht : t ∈ R) (hv : v ∈ R)
    (hv' : ∃ v' : ℍ[ℚ, a, b], v' ∈ R ∧ v * v' = 1 ∧ v' * v = 1)
    (hlev : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) :
    t * v ∈ R ∧ nrd (t * v) = nrd t * nrd v ∧
      ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * (t * v) = x) ↔ ∃ j ∈ J', j * (t * v) = x := by sorry
