-- Prove2me | Theorems.Thm_QuaternionAlgebra_relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral
-- name    : QuaternionAlgebra.relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/69bf917b-dad1-546d-8d58-363c1d3ffbf3
-- title:
--   Local index ℓⁿ of an Eichler order in a maximal order
-- statement:
--   Let $a,b\in\mathbb{Q}$ both be nonzero, let $v$ be a point of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$, and let $\ell$ be a prime with $\ell\in v$, so that $v$ is the place above $\ell$ and $v$-adic completion gives $\mathbb{Q}_\ell$ with valuation ring $\mathcal{O}_v$. Let $\varphi$ be a ring isomorphism $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v\cong M_2(\mathbb{Q}_v)$ sending $1\otimes r$ to the scalar matrix $r\cdot 1$ for every $r\in\mathbb{Q}_v$. Let $A$ be an additive subgroup of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ consisting exactly of those $z$ with all entries of $\varphi(z)$ in $\mathcal{O}_v$. Let $k\in\mathrm{GL}_2(\mathbb{Q}_v)$ have all entries of $k$ and of $k^{-1}$ in $\mathcal{O}_v$, let $n\in\mathbb{N}$, write $D=\mathrm{diag}(1,\ell^n)$, and let $B$ be an additive subgroup consisting exactly of those $z$ with all entries of $\varphi(z)$ in $\mathcal{O}_v$ and all entries of $D^{-1}k^{-1}\varphi(z)kD$ in $\mathcal{O}_v$ (the inverse diagonal being written as $\mathrm{diag}(1,(\ell^{n})^{-1})$). Then the relative index of $B$ in $A$, that is the index of $A\cap B$ in $A$, equals $\ell^n$.
--
--   This is the local index computation for an Eichler order of level $\ell^n$ inside a maximal order: $A$ and its conjugate by $kD$ are two maximal orders of $M_2(\mathbb{Q}_\ell)$ at distance $n$ in the Bruhat–Tits tree, and their intersection has index $\ell^n$ in the first. It is used in the analysis of the local type of a normalised connecting idele, in [`QuaternionAlgebra.IsMaximalOrder.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq`](thm.html#QuaternionAlgebra.IsMaximalOrder.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain NumberField

theorem QuaternionAlgebra.relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral
    {a b : ℚ} (hab : a ≠ 0 ∧ b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (A : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hA : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ∈ A ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hki : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ)
    (n : ℕ) (B : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hB : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ∈ B ↔
      (∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ) ∧
        ∀ i j, (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((ℓ : ℕ) : v.adicCompletion ℚ) ^ n)⁻¹] *
          ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * φ z *
          (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
          Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((ℓ : ℕ) : v.adicCompletion ℚ) ^ n]) i j ∈ v.adicCompletionIntegers ℚ) :
    B.relIndex A = ℓ ^ n := by sorry
