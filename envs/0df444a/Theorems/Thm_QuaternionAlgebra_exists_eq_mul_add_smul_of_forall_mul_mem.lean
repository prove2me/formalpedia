-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_eq_mul_add_smul_of_forall_mul_mem
-- name    : QuaternionAlgebra.exists_eq_mul_add_smul_of_forall_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/74388da8-a2bf-5729-a3b4-c1d4e4487571
-- title:
--   Right multiplication by c is onto L₀ modulo ℓΛ
-- statement:
--   Let $a,b\in\mathbb Q$ and let $\Lambda$ be a $\mathbb Z$-submodule of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ which is closed under multiplication ($x,y\in\Lambda\Rightarrow xy\in\Lambda$) and finitely generated. Let $\ell$ be a positive natural number, and let $L_0$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,a,b]$ with $L_0\le\Lambda$ and such that $\ell\cdot x\in L_0$ for every $x\in\Lambda$, i.e. $\ell\Lambda\subseteq L_0\subseteq\Lambda$. Let $c,d\in\Lambda$ be mutually inverse modulo $\ell\Lambda$, in the sense that $cd-1=\ell\cdot y$ and $dc-1=\ell\cdot y'$ for some $y,y'\in\Lambda$, and assume that $L_0$ is stable under right multiplication by $c$: $x\in L_0\Rightarrow xc\in L_0$. The conclusion is that every $y\in\Lambda$ lying in $L_0$ can be written as $y=xc+\ell\cdot z$ with $x,z\in\Lambda$ and $x\in L_0$; all scalar multiplications by $\ell$ are taken with the rational scalar $(\ell:\mathbb Q)$ inside $\mathbb H[\mathbb Q,a,b]$.
--
--   An elementary lattice statement for a multiplicatively closed finitely generated additive subgroup (an order, up to unitality) of a rational quaternion algebra: right multiplication by an element invertible modulo $\ell$ permutes the classes modulo $\ell\Lambda$ of a right-$c$-stable subgroup $L_0$. It is used in the Čerednik–Drinfeld quaternionic moduli part of the development, in the analysis of level-$\ell$ structures and the closedness of the images of the corresponding maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_eq_mul_add_smul_of_forall_mul_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_eq_mul_add_smul_of_forall_mul_mem
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ → y ∈ Λ → x * y ∈ Λ) (hfg : Λ.FG)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ)
    (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (c d : ↥Λ)
    (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (hdc : ∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (hL₀c : ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (c : ℍ[ℚ, a, b]) ∈ L₀) :
    ∀ y : ↥Λ, (y : ℍ[ℚ, a, b]) ∈ L₀ →
      ∃ x z : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        (y : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) + (ℓ : ℚ) • (z : ℍ[ℚ, a, b]) := by sorry
