-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne
-- name    : QuaternionAlgebra.exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/b8e42c52-61bf-5bb5-9ad6-23bcba14875f
-- title:
--   Maximal order modulo ℓ^m is M₂(ℤ/ℓ^m)
-- statement:
--   Let $a,b$ be rationals and let $B=\mathbb{H}[\mathbb{Q},a,b]$ be the associated quaternion algebra. Let $q,q'$ be primes and assume `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. that $0<a$ or $0<b$, and that for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division ring (every nonzero element is a unit) precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order: $\Lambda$ contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$ and is finitely generated over $\mathbb{Z}$, and every order $\Lambda'$ containing $\Lambda$ equals $\Lambda$. Let $\ell$ be a prime with $\ell\neq q$ and $\ell\neq q'$, and let $m$ be a nonzero natural number. Then there is a $\mathbb{Z}$-linear map $\varphi\colon\Lambda\to M_2(\mathbb{Z}/\ell^m)$ such that $\varphi(1)=1$, such that $\varphi$ carries the product of any $x,y\in\Lambda$ (taken in $B$, together with a proof that it lies in $\Lambda$) to $\varphi(x)\varphi(y)$, such that $\varphi$ is surjective, and such that for $x\in\Lambda$ one has $\varphi(x)=0$ if and only if $x=\ell^m\,y$ in $B$ for some $y\in\Lambda$.
--
--   This identifies $\Lambda/\ell^m\Lambda$ with $M_2(\mathbb{Z}/\ell^m)$ for a maximal order $\Lambda$ in an indefinite rational quaternion algebra and a prime $\ell$ of good (split) reduction, the unital ring isomorphism being packaged as a surjective $\mathbb{Z}$-linear map that is unital and multiplicative with prescribed kernel. It is used in the construction of transverse level structures of $\ell$-power level on fake elliptic curves attached to the quaternion algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (m : ℕ) [NeZero m] :
    ∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m)),
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧
      Function.Surjective φ ∧
      (∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = ((ℓ ^ m : ℕ) : ℚ) • (y : ℍ[ℚ, a, b])) := by sorry
