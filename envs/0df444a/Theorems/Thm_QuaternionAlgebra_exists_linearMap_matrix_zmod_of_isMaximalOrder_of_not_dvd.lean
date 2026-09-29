-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd
-- name    : QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/17544fa8-a6e8-5d23-b36b-51333450de12
-- title:
--   Maximal order reduces mod N onto M₂(ℤ/N)
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q,q'$ be primes, and suppose that the quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has every nonzero element a unit precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule that is a maximal order, meaning that $1\in\Lambda$, $\Lambda$ is closed under multiplication, the $\mathbb{Q}$-span of $\Lambda$ is all of $B$ and $\Lambda$ is finitely generated, and that every order $\Lambda'$ with $\Lambda\subseteq\Lambda'$ equals $\Lambda$. Let $N$ be a nonzero natural number with $q\nmid N$ and $q'\nmid N$. Then there exists a $\mathbb{Z}$-linear map $\varphi:\Lambda\to M_2(\mathbb{Z}/N\mathbb{Z})$ such that $\varphi(1)=1$ (for any proof that $1\in\Lambda$), such that $\varphi(xy)=\varphi(x)\varphi(y)$ for all $x,y\in\Lambda$ and any proof that the product $xy$ lies in $\Lambda$, such that $\varphi$ is surjective, and such that for $x\in\Lambda$ one has $\varphi(x)=0$ if and only if $x=N\cdot y$ for some $y\in\Lambda$. Thus $\varphi$ induces a ring isomorphism $\Lambda/N\Lambda\cong M_2(\mathbb{Z}/N\mathbb{Z})$, stated here as a linear map with multiplicative and kernel properties rather than as an isomorphism of rings.
--
--   This is the standard fact that a maximal order in an indefinite rational quaternion algebra of discriminant $qq'$ is split at every prime not dividing $qq'$, so that its reduction modulo any $N$ coprime to $qq'$ is the full matrix algebra $M_2(\mathbb{Z}/N\mathbb{Z})$; the prime case $N=\ell$ is [`QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne`](thm.html#QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne). It supplies the level structures on fake elliptic curves used in the Čerednik–Drinfeld part of the development, and is cited in the construction of Eichler orders and in the nonemptiness statements for the associated Shimura curves over $\overline{\mathbb{Q}}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct
open QuaternionAlgebra
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) :
    ∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N),
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧
      Function.Surjective φ ∧
      (∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b])) := by sorry
