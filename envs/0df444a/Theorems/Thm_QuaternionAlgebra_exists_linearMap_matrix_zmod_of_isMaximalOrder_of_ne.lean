-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
-- name    : QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/09187c56-a55c-54c6-b80b-dd1c3e16d4d4
-- title:
--   Reduction of a maximal quaternion order modulo ℓ
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q,q'$ be primes. Assume the hypothesis `IsIndefiniteRamifiedExactlyAt a b q q'`: that $0<a$ or $0<b$, and that for every height one prime $v$ of the ring of integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) precisely when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $B=\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order, i.e. $1\in\Lambda$, $\Lambda$ is closed under multiplication, $\Lambda$ spans $B$ over $\mathbb{Q}$ and is finitely generated, and every such $\Lambda'$ with $\Lambda\le\Lambda'$ equals $\Lambda$. Let $\ell$ be a prime with $\ell\ne q$ and $\ell\ne q'$. Then there is a $\mathbb{Z}$-linear map $\varphi\colon\Lambda\to M_2(\mathbb{Z}/\ell)$ such that: $\varphi(1)=1$ (for any proof that $1\in\Lambda$); for all $x,y\in\Lambda$ and any proof that $xy\in\Lambda$, $\varphi(xy)=\varphi(x)\varphi(y)$; $\varphi$ is surjective; and for $x\in\Lambda$, $\varphi(x)=0$ if and only if $x=\ell y$ in $B$ for some $y\in\Lambda$. Thus $\varphi$ identifies $\Lambda/\ell\Lambda$ with $M_2(\mathbb{F}_\ell)$.
--
--   This is the standard splitting of a maximal order in the indefinite rational quaternion algebra of discriminant $qq'$ at a prime $\ell$ of good reduction: $\Lambda\otimes\mathbb{Z}_\ell\cong M_2(\mathbb{Z}_\ell)$, whence $\Lambda/\ell\Lambda\cong M_2(\mathbb{F}_\ell)$. Since the order is carried here as a $\mathbb{Z}$-lattice with no ring structure on the carrier, unitality and multiplicativity are stated relative to arbitrary membership proofs; the result is used in the Čerednik–Drinfeld analysis of fake elliptic curves, where the action of $\Lambda$ on $\ell$-torsion factors through $\varphi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    ∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ),

      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧

      Function.Surjective φ ∧

      (∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) := by sorry
