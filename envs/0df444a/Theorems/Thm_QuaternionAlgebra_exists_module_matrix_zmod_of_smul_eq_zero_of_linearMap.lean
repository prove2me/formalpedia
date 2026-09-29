-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_module_matrix_zmod_of_smul_eq_zero_of_linearMap
-- name    : QuaternionAlgebra.exists_module_matrix_zmod_of_smul_eq_zero_of_linearMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/5ea2b56b-2fb0-5b9a-bc65-0e357911dffc
-- title:
--   An ℓ-torsion Λ-action factors through M₂(𝔽_ℓ)
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and let $\ell$ be a natural number carrying a `Fact` that it is prime. Suppose given a $\mathbb{Z}$-linear map $\varphi:\Lambda\to M_2(\mathbb{Z}/\ell)$ which is unital (whenever $1\in\Lambda$, $\varphi(1)=1$), multiplicative in the sense that $\varphi(xy)=\varphi(x)\varphi(y)$ whenever $x,y\in\Lambda$ and the product $xy$ again lies in $\Lambda$, surjective, and whose kernel is exactly $\ell\Lambda$: $\varphi(x)=0$ iff $x=\ell y$ in $\mathbb{H}[\mathbb{Q},a,b]$ for some $y\in\Lambda$. Assume moreover $1\in\Lambda$ and that $\Lambda$ is closed under multiplication. Let $V$ be an additive commutative group in an arbitrary universe with $\ell v=0$ for all $v\in V$, and let $\mathrm{act}$ assign to each $x\in\Lambda$ an additive endomorphism of $V$, subject to $\mathrm{act}(1)=\mathrm{id}_V$, $\mathrm{act}(xy)=\mathrm{act}(x)\circ\mathrm{act}(y)$ and $\mathrm{act}(x+y)=\mathrm{act}(x)+\mathrm{act}(y)$. The conclusion asserts the existence of a module structure on $V$ over the ring $M_2(\mathbb{Z}/\ell)$ such that, for this structure, $\varphi(m)\cdot v=\mathrm{act}(m)(v)$ for all $m\in\Lambda$ and $v\in V$. Note that $\Lambda$ is only assumed to be a multiplicatively closed $\mathbb{Z}$-submodule containing $1$; no maximality or lattice condition enters.
--
--   This is the passage from a $\Lambda$-action on an $\ell$-torsion abelian group to a genuine $M_2(\mathbb{F}_\ell)$-module structure, the point being that $\Lambda$-stable subgroups are then exactly the $M_2(\mathbb{F}_\ell)$-submodules, so that the structure theory of modules over a matrix ring becomes available. It is the universe-polymorphic form used in the Čerednik–Drinfel'd part of the argument, where $V$ is a group of $\ell$-torsion points of a fake elliptic curve; it is applied in [`CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_of_isLevelIsogeny_of_exists_factorsThrough_ne_one`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_of_isLevelIsogeny_of_exists_factorsThrough_ne_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_module_matrix_zmod_of_smul_eq_zero_of_linearMap.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped Quaternion

theorem QuaternionAlgebra.exists_module_matrix_zmod_of_smul_eq_zero_of_linearMap
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ))
    (hφ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1)
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (hmul : ∀ x y : ↥Λ, (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ)
    (V : Type u) [AddCommGroup V] (hV : ∀ v : V, ℓ • v = 0)
    (act : ↥Λ → V →+ V)
    (hact1 : act ⟨1, h1⟩ = AddMonoidHom.id V)
    (hactmul : ∀ x y : ↥Λ, act ⟨_, hmul x y⟩ = (act x).comp (act y))
    (hactadd : ∀ x y : ↥Λ, act (x + y) = act x + act y) :
    ∃ inst : Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V,
      ∀ (m : ↥Λ) (v : V), @HSMul.hSMul (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V V (@instHSMul _ _ inst.toSMul) (φ m) v = act m v := by sorry
