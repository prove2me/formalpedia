-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt_of_ne
-- name    : QuaternionAlgebra.exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/e1712120-0605-5388-ad3a-78fa5e0b3fb4
-- title:
--   Maximal order of a definite quaternion algebra modulo ℓ^m
-- statement:
--   Let $c,d\in\mathbb{Q}$ and let $r$ be a prime. Assume that the quaternion algebra $\mathbb{H}[\mathbb{Q},c,d]$ is definite and ramified exactly at $r$, that is: $c<0$, $d<0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the base change $\mathbb{H}[\mathbb{Q},c,d]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible if and only if $r$ lies in the prime ideal of $v$. Let $O$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},c,d]$ that is a maximal order, i.e. $O$ contains $1$, is closed under multiplication, has $\mathbb{Q}$-span the whole algebra and is finitely generated over $\mathbb{Z}$, and every order containing $O$ equals $O$. Let $\ell$ be a prime with $\ell\neq r$ and let $m$ be a nonzero natural number. Then there exists a $\mathbb{Z}$-linear map $\varphi\colon O\to M_2(\mathbb{Z}/\ell^m\mathbb{Z})$ such that: $\varphi(1)=1$ (for any proof that $1\in O$); for all $x,y\in O$ and any proof that $xy\in O$, $\varphi(xy)=\varphi(x)\varphi(y)$; $\varphi$ is surjective; and for $x\in O$ one has $\varphi(x)=0$ if and only if $x=\ell^m y$ in $\mathbb{H}[\mathbb{Q},c,d]$ for some $y\in O$. Thus $\varphi$ presents an isomorphism $O/\ell^m O\cong M_2(\mathbb{Z}/\ell^m\mathbb{Z})$, with the multiplicative structure recorded pointwise rather than through a ring structure on $O$.
--
--   This is the local-global consequence of the splitting $O\otimes_{\mathbb{Z}}\mathbb{Z}_\ell\cong M_2(\mathbb{Z}_\ell)$ at a prime $\ell$ at which the definite algebra is unramified, in the concrete form of a surjection of $O$ onto $M_2(\mathbb{Z}/\ell^m\mathbb{Z})$ with kernel $\ell^m O$. It feeds the corresponding statement for a modulus not divisible by the ramified prime, and through it the construction of mod-$\ell^m$ Hecke and Galois data attached to definite quaternionic automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt_of_ne.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt_of_ne
    {c d : ℚ} {r : ℕ} [Fact r.Prime]
    (hH' : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d r)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : QuaternionAlgebra.IsMaximalOrder O)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓr : ℓ ≠ r) (m : ℕ) [NeZero m] :
    ∃ φ : ↥O →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m)),
      (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
          φ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = φ x * φ y) ∧
      Function.Surjective φ ∧
      (∀ x : ↥O, φ x = 0 ↔ ∃ y : ↥O, (x : ℍ[ℚ, c, d]) = ((ℓ ^ m : ℕ) : ℚ) • (y : ℍ[ℚ, c, d])) := by sorry
