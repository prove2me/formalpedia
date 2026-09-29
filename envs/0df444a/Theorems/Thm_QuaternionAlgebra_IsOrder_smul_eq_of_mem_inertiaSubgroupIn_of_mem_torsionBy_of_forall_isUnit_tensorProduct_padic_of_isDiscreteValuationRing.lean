-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_smul_eq_of_mem_inertiaSubgroupIn_of_mem_torsionBy_of_forall_isUnit_tensorProduct_padic_of_isDiscreteValuationRing
-- name    : QuaternionAlgebra.IsOrder.smul_eq_of_mem_inertiaSubgroupIn_of_mem_torsionBy_of_forall_isUnit_tensorProduct_padic_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/578643a1-b551-506c-b5db-0d6fe41c0d77
-- title:
--   Ohta's theorem for inertia over a discrete valuation ring
-- statement:
--   Let $a,b\in\mathbb Q$ and let $\Lambda$ be a $\mathbb Z$-submodule of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ which is an order in the sense that $1\in\Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb Q$-span is all of $\mathbb H[\mathbb Q,a,b]$, and it is finitely generated. Let $\ell$ be a prime such that every non-zero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_\ell$ is a unit. Let $R$ be a discrete valuation domain with finite residue field, $K$ a fraction field of $R$ and $\Omega$ an algebraic closure of $K$, and let $M$ be an additive commutative group carrying a distributive action of the group $\Omega\simeq_{\text{alg}[K]}\Omega$ of $K$-automorphisms of $\Omega$. Assume: for every $n$ the $\ell^n$-torsion submodule $\operatorname{torsionBy}_{\mathbb Z}(M,\ell^n)$ has exactly $(\ell^n)^4$ elements; for every $n$ there is an intermediate field $F_n$ of $\Omega/K$, finite over $K$, such that every automorphism fixing $F_n$ pointwise fixes the $\ell^n$-torsion pointwise; and $\Lambda$ acts by a map $i$ sending each element of $\Lambda$ to an additive endomorphism of $M$, with $i(1)=\mathrm{id}_M$, $i(xy)=i(x)\circ i(y)$ for $x,y\in\Lambda$, $i(x+y)=i(x)+i(y)$, and $\sigma\cdot i(x)m=i(x)(\sigma\cdot m)$ for all automorphisms $\sigma$, all $x\in\Lambda$ and all $m\in M$. Let $c$ satisfy $3\le\ell^c$ and let $F$ be an intermediate field of $\Omega/K$, finite over $K$, such that every automorphism fixing $F$ pointwise fixes the $\ell^c$-torsion of $M$ pointwise. Assume $\ell$ is a unit in $R$, and let $A$ be a valuation subring of $\Omega$ containing the image of $R$. Then for every $\sigma$ fixing $F$ pointwise and lying in `inertiaSubgroupIn`, the image in $\Omega\simeq_{\text{alg}[K]}\Omega$ of the inertia subgroup of $A$ over $K$ inside the decomposition subgroup, and for every $n$ and every $m$ in the $\ell^n$-torsion of $M$, one has $\sigma\cdot m=m$.
--
--   This is the statement sometimes attributed to Ohta: an inertia element that fixes the $\ell^c$-torsion of a quaternionically multiplied $\ell$-divisible module with $\ell^c\ge 3$ fixes all of its $\ell$-power torsion, here in the generality of an arbitrary discrete valuation ring with finite residue field in which $\ell$ is invertible, rather than a number field. It is the Galois-theoretic input to [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn_of_forall_isUnit_tensorProduct_padic`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn_of_forall_isUnit_tensorProduct_padic), and through it to the reduction theory of fake elliptic curves with level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_smul_eq_of_mem_inertiaSubgroupIn_of_mem_torsionBy_of_forall_isUnit_tensorProduct_padic_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct

theorem QuaternionAlgebra.IsOrder.smul_eq_of_mem_inertiaSubgroupIn_of_mem_torsionBy_of_forall_isUnit_tensorProduct_padic_of_isDiscreteValuationRing
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] ℚ_[ℓ], x ≠ 0 → IsUnit x)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {M : Type} [AddCommGroup M] [DistribMulAction (Ω ≃ₐ[K] Ω) M]
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ 4)
    (hcont : ∀ n : ℕ, ∃ Fn : IntermediateField K Ω, FiniteDimensional K ↥Fn ∧
      ∀ σ : Ω ≃ₐ[K] Ω, (∀ x ∈ Fn, σ x = x) →
        ∀ m ∈ Submodule.torsionBy ℤ M ((ℓ ^ n : ℕ) : ℤ), σ • m = m)
    (i : ↥Λ → M →+ M) (hi_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, i ⟨1, h⟩ = AddMonoidHom.id M)
    (hi_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      i ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (i x).comp (i y))
    (hi_add : ∀ x y : ↥Λ, i (x + y) = i x + i y)
    (hi_smul : ∀ (σ : Ω ≃ₐ[K] Ω) (x : ↥Λ) (m : M), σ • i x m = i x (σ • m))
    {c : ℕ} (hc : 3 ≤ ℓ ^ c) (F : IntermediateField K Ω) [FiniteDimensional K ↥F]
    (hlevel : ∀ σ : Ω ≃ₐ[K] Ω, (∀ x ∈ F, σ x = x) →
      ∀ m ∈ Submodule.torsionBy ℤ M ((ℓ ^ c : ℕ) : ℤ), σ • m = m)
    (hℓ : IsUnit ((ℓ : ℕ) : R))
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A)
    {σ : Ω ≃ₐ[K] Ω} (hσF : ∀ x ∈ F, σ x = x) (hσ : σ ∈ A.inertiaSubgroupIn K)
    (n : ℕ) (m : M) (hm : m ∈ Submodule.torsionBy ℤ M ((ℓ ^ n : ℕ) : ℤ)) : σ • m = m := by sorry
