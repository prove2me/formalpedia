-- Prove2me | Theorems.Thm_QuaternionAlgebra_forall_conj_mem_iff_or_exists_eq_mul_one_tmul_of_forall_conj_natCast_mul_mem
-- name    : QuaternionAlgebra.forall_conj_mem_iff_or_exists_eq_mul_one_tmul_of_forall_conj_natCast_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/e71977b7-28a0-5f5e-b610-49cf35904d52
-- title:
--   Normaliser or elementary divisors (1,ℓ) for a local conjugation
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and a height one prime $v$ of the ring of integers of $\mathbb{Q}$, and let $\ell$ be a prime natural number whose image lies in the ideal $v$. Let $\varphi$ be a ring isomorphism $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v\cong M_2(\mathbb{Q}_v)$, where $\mathbb{Q}_v$ is the $v$-adic completion, and assume $\varphi$ is scalar on the second factor: $\varphi(1\otimes r)=r\cdot 1$ for every $r\in\mathbb{Q}_v$. Let $h\in \mathrm{GL}_2(\mathbb{Q}_v)$ and let $O$ be an additive subgroup of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ whose members are exactly those $x$ for which all four entries of $h^{-1}\,\varphi(x)\,h$ lie in the valuation ring $\mathcal{O}_v$, i.e. $O=\varphi^{-1}\bigl(h\,M_2(\mathcal{O}_v)\,h^{-1}\bigr)$. Let $\nu$ be a unit of the tensor product such that $\nu^{-1}\bigl((1\otimes\ell)\,y\bigr)\nu\in O$ for every $y\in O$. The conclusion is a disjunction: either $\nu$ normalises $O$, in the sense that $\nu^{-1}y\nu\in O\iff y\in O$ for all $y$; or there are a scalar $s\in\mathbb{Q}_v$ and a unit $\nu_0$ with $\nu=\nu_0\,(1\otimes s)$, $\nu_0\in O$, $(1\otimes\ell)\,\nu_0^{-1}\in O$, $\nu_0^{-1}\notin O$ and $(1\otimes\ell^{-1})\,\nu_0\notin O$.
--
--   This is the local consequence of the Cartan decomposition $\mathrm{GL}_2(\mathbb{Q}_v)=\mathrm{GL}_2(\mathcal{O}_v)\,\mathrm{diag}(\ell^{a},\ell^{b})\,\mathrm{GL}_2(\mathcal{O}_v)$ describing the elements that carry a vertex of the Bruhat–Tits tree to itself or to a neighbour: a unit whose conjugation moves the maximal order $O$ by at most one step either normalises $O$ or, up to a central scalar, has elementary divisors $(1,\ell)$. It is used, via [`LocalGL2.exists_cartanRel_cartanDiag`](thm.html#LocalGL2.exists_cartanRel_cartanDiag), to isolate the degree-$\ell$ part of an idèle in [`QuaternionAlgebra.exists_eq_mul_mem_primeHeckeSet_mem_normalizer_meetOrder_eq_of_isEichlerOrder_meetOrder`](thm.html#QuaternionAlgebra.exists_eq_mul_mem_primeHeckeSet_mem_normalizer_meetOrder_eq_of_isEichlerOrder_meetOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_forall_conj_mem_iff_or_exists_eq_mul_one_tmul_of_forall_conj_natCast_mul_mem.lean

import Mathlib
import Definitions.Def_Submodule_LocalBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.forall_conj_mem_iff_or_exists_eq_mul_one_tmul_of_forall_conj_natCast_mul_mem
    {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (h : GL (Fin 2) (v.adicCompletion ℚ))
    (O : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hO : ∀ x, x ∈ O ↔ ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)
    (ν : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ)
    (hν : ∀ y ∈ O, ((ν⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) *
      (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)) * y) * ν ∈ O) :
    (∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        ((ν⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * y * ν ∈ O ↔
          y ∈ O) ∨
      ∃ (s : v.adicCompletion ℚ) (ν₀ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ),
        (ν : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = ν₀ * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s) ∧
        (ν₀ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ O ∧
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)) *
          ((ν₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ O ∧
        ((ν₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ O ∧
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)⁻¹) * (ν₀ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ O := by sorry
