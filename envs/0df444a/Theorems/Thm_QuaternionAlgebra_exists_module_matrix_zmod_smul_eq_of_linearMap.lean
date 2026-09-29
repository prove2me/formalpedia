-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_module_matrix_zmod_smul_eq_of_linearMap
-- name    : QuaternionAlgebra.exists_module_matrix_zmod_smul_eq_of_linearMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/419d8aa8-6958-5210-aaba-d5b2f60f3bc2
-- title:
--   A Λ-action killed by ℓ descends to M₂(𝔽_ℓ)
-- statement:
--   Fix rationals $a,b$ and write $\mathbb{H}[\mathbb{Q},a,b]$ for the associated quaternion algebra over $\mathbb{Q}$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$, let $\ell$ be a prime, and let $\varphi : \Lambda \to M_2(\mathbb{Z}/\ell)$ be a $\mathbb{Z}$-linear map subject to: $\varphi(1) = 1$ whenever $1 \in \Lambda$; $\varphi(xy) = \varphi(x)\varphi(y)$ for all $x,y \in \Lambda$ whose product lies in $\Lambda$; $\varphi$ is surjective; and $\varphi(x) = 0$ if and only if $x = \ell y$ for some $y \in \Lambda$ (the kernel is $\ell\Lambda$). Assume moreover $1 \in \Lambda$ and that $\Lambda$ is closed under multiplication. Let $V$ be an additive abelian group with $\ell v = 0$ for all $v \in V$, and let $\mathrm{act}$ assign to each $x \in \Lambda$ an additive endomorphism of $V$, in such a way that $\mathrm{act}(1)$ is the identity, $\mathrm{act}(xy) = \mathrm{act}(x) \circ \mathrm{act}(y)$, and $\mathrm{act}(x+y) = \mathrm{act}(x) + \mathrm{act}(y)$. The conclusion asserts the existence of a module structure on $V$ over the ring $M_2(\mathbb{Z}/\ell)$ for which $\varphi(m) \cdot v = \mathrm{act}(m)(v)$ for all $m \in \Lambda$ and $v \in V$.
--
--   This is the change-of-rings step that converts an action of a quaternionic lattice $\Lambda$ on an $\ell$-torsion abelian group into a genuine $M_2(\mathbb{F}_\ell)$-module structure, along the identification $\Lambda/\ell\Lambda \cong M_2(\mathbb{F}_\ell)$ recorded by $\varphi$. It is used in the study of torsion points of fake elliptic curves, where $\Lambda$-stable subgroups of the $\ell$-torsion are thereby recognised as $M_2(\mathbb{F}_\ell)$-submodules and counting results for such modules become applicable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_module_matrix_zmod_smul_eq_of_linearMap.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_module_matrix_zmod_smul_eq_of_linearMap
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ))
    (hφ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1)
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (hmul : ∀ x y : ↥Λ, (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ)
    (V : Type) [AddCommGroup V] (hV : ∀ v : V, ℓ • v = 0)
    (act : ↥Λ → V →+ V)
    (hact1 : act ⟨1, h1⟩ = AddMonoidHom.id V)
    (hactmul : ∀ x y : ↥Λ, act ⟨_, hmul x y⟩ = (act x).comp (act y))
    (hactadd : ∀ x y : ↥Λ, act (x + y) = act x + act y) :
    ∃ inst : Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V,
      ∀ (m : ↥Λ) (v : V), @HSMul.hSMul (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V V (@instHSMul _ _ inst.toSMul) (φ m) v = act m v := by sorry
