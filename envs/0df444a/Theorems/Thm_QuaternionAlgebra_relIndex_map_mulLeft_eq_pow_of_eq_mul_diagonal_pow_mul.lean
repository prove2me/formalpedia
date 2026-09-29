-- Prove2me | Theorems.Thm_QuaternionAlgebra_relIndex_map_mulLeft_eq_pow_of_eq_mul_diagonal_pow_mul
-- name    : QuaternionAlgebra.relIndex_map_mulLeft_eq_pow_of_eq_mul_diagonal_pow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/6dba7c29-264b-5465-8e79-88c127fe7c0d
-- title:
--   Index of a left translate of M₂(ℤᵥ)
-- statement:
--   Let $a,b\in\mathbb{Q}$ with $a\neq 0$ and $b\neq 0$, let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, let $\ell$ be a prime number with $\ell\in v$, and write $\mathbb{Q}_v$ for the $v$-adic completion of $\mathbb{Q}$ and $\mathbb{Z}_v$ for its ring of $v$-adic integers. Suppose given a ring isomorphism $\varphi : \mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v \xrightarrow{\sim} M_2(\mathbb{Q}_v)$ which is $\mathbb{Q}_v$-scalar-preserving in the sense that $\varphi(1\otimes r)=r\cdot 1$ for all $r\in\mathbb{Q}_v$, and an additive subgroup $A$ of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ characterised by the property that $z\in A$ if and only if every entry $\varphi(z)_{ij}$ lies in $\mathbb{Z}_v$. Let $k_1,k_2\in \mathrm{GL}_2(\mathbb{Q}_v)$ be such that all entries of $k_1, k_1^{-1}, k_2, k_2^{-1}$ lie in $\mathbb{Z}_v$, let $e_1,e_2\in\mathbb{N}$, and let $g$ be an element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ with $\varphi(g)=k_1\,\mathrm{diag}(\ell^{e_1},\ell^{e_2})\,k_2$. Then the relative index of the image $gA$ of $A$ under left multiplication by $g$ inside $A$ equals $\ell^{2(e_1+e_2)}$.
--
--   This is the local index computation $[\mathcal{O}_v : g\mathcal{O}_v] = \ell^{2(e_1+e_2)}$ for the matrix order $\mathcal{O}_v \cong M_2(\mathbb{Z}_v)$ and an element $g$ with elementary divisors $(\ell^{e_1},\ell^{e_2})$, i.e. the Cartan/Smith normal form shape of $\varphi(g)$; equivalently $[\mathcal{O}:g\mathcal{O}]=|\det\varphi(g)|_v^{-2}$. It feeds the local analysis of Hecke double cosets for quaternionic automorphic forms, being used in the index criteria [`QuaternionAlgebra.exists_ofFiniteIdele_mul_eq_ofFiniteIdele_mul_mul_iff_relIndex_eq_sq_and_forall_not_le_zsmul`](thm.html#QuaternionAlgebra.exists_ofFiniteIdele_mul_eq_ofFiniteIdele_mul_mul_iff_relIndex_eq_sq_and_forall_not_le_zsmul) and [`QuaternionAlgebra.relIndex_ofFiniteIdele_mul_eq_sq_of_mem_finiteAdeleBox_of_relIndex_inf_conjByFiniteIdele_eq`](thm.html#QuaternionAlgebra.relIndex_ofFiniteIdele_mul_eq_sq_of_mem_finiteAdeleBox_of_relIndex_inf_conjByFiniteIdele_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_relIndex_map_mulLeft_eq_pow_of_eq_mul_diagonal_pow_mul.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain NumberField

theorem QuaternionAlgebra.relIndex_map_mulLeft_eq_pow_of_eq_mul_diagonal_pow_mul
    {a b : ℚ} (hab : a ≠ 0 ∧ b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (A : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hA : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ∈ A ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ)
    (k₁ k₂ : GL (Fin 2) (v.adicCompletion ℚ))
    (hk₁ : ∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hk₁i : ∀ i j, ((k₁⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ)
    (hk₂ : ∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hk₂i : ∀ i j, ((k₂⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ)
    (e₁ e₂ : ℕ) (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
    (hg : φ g = (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
      Matrix.diagonal ![((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₁, ((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₂] * (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) :
    (A.map (AddMonoidHom.mulLeft g)).relIndex A = ℓ ^ (2 * (e₁ + e₂)) := by sorry
