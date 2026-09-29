-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_smul_eq_of_mem_inertiaSubgroupIn_of_mem_torsionBy_of_forall_isUnit_tensorProduct_padic
-- name    : QuaternionAlgebra.IsOrder.smul_eq_of_mem_inertiaSubgroupIn_of_mem_torsionBy_of_forall_isUnit_tensorProduct_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/5487e942-dd75-5d37-9dd3-814a76c5dc1a
-- title:
--   Inertia away from ℓ acts trivially on ℓ-power torsion
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of [`QuaternionAlgebra.IsOrder`](def/QuaternionAlgebra_Order.html#L11): $1\in\Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb{Q}$-span is all of $B$, and it is finitely generated over $\mathbb{Z}$. Let $\ell$ be a prime such that every non-zero element of $B\otimes_{\mathbb{Q}}\mathbb{Q}_{\ell}$ is a unit, and let $K\subseteq\overline{\mathbb{Q}}$ be an intermediate field of finite degree over $\mathbb{Q}$. Let $M$ be an abelian group carrying a distributive action of $G_K=\operatorname{Aut}_K(\overline{\mathbb{Q}})$ such that (i) for every $n$ the $\ell^n$-torsion submodule $M[\ell^n]$ has exactly $(\ell^n)^4$ elements; (ii) for every $n$ there is an intermediate field $F_n$ of finite degree over $\mathbb{Q}$ such that each $\sigma\in G_K$ fixing $F_n$ pointwise fixes $M[\ell^n]$ pointwise. Let $i$ assign to each $x\in\Lambda$ an additive endomorphism $i(x)$ of $M$, with $i(1)=\mathrm{id}$, $i(xy)=i(x)\circ i(y)$ for $x,y\in\Lambda$, $i(x+y)=i(x)+i(y)$, and $\sigma\cdot i(x)m=i(x)(\sigma\cdot m)$ for all $\sigma\in G_K$, $x\in\Lambda$, $m\in M$. Let $c$ satisfy $\ell^c\geq 3$ and let $F\subseteq\overline{\mathbb{Q}}$ be an intermediate field of finite degree over $\mathbb{Q}$ containing $K$ such that every $\sigma\in G_K$ fixing $F$ pointwise fixes $M[\ell^c]$ pointwise. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ in which the image of $\ell$ is a unit, and let $\sigma\in G_K$ fix $F$ pointwise and lie in the inertia subgroup of $A$ over $K$, viewed inside $G_K$ as the image of the inertia subgroup under the inclusion of the decomposition subgroup. Then $\sigma\cdot m=m$ for every $n$ and every $m\in M[\ell^n]$.
--
--   This is the Galois-theoretic core of potential good reduction for abelian surfaces with quaternionic multiplication (fake elliptic curves): over the field cut out by the $\ell^c$-torsion, inertia at a place where $\ell$ is invertible acts trivially on the whole $\ell$-divisible torsion, so that the associated $\ell$-adic representation is unramified there. It is used in the Čerednik–Drinfeld part of the development, in the construction of an intermediate field over which the relevant abelian scheme data is obtained by pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_smul_eq_of_mem_inertiaSubgroupIn_of_mem_torsionBy_of_forall_isUnit_tensorProduct_padic.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct

theorem QuaternionAlgebra.IsOrder.smul_eq_of_mem_inertiaSubgroupIn_of_mem_torsionBy_of_forall_isUnit_tensorProduct_padic
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] ℚ_[ℓ], x ≠ 0 → IsUnit x)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    {M : Type} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ) M]
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ 4)
    (hcont : ∀ n : ℕ, ∃ Fn : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ ↥Fn ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ, (∀ x ∈ Fn, σ x = x) →
        ∀ m ∈ Submodule.torsionBy ℤ M ((ℓ ^ n : ℕ) : ℤ), σ • m = m)
    (i : ↥Λ → M →+ M) (hi_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, i ⟨1, h⟩ = AddMonoidHom.id M)
    (hi_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      i ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (i x).comp (i y))
    (hi_add : ∀ x y : ↥Λ, i (x + y) = i x + i y)
    (hi_smul : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ) (x : ↥Λ) (m : M), σ • i x m = i x (σ • m))
    {c : ℕ} (hc : 3 ≤ ℓ ^ c) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] (hKF : K ≤ F)
    (hlevel : ∀ σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ, (∀ x ∈ F, σ x = x) →
      ∀ m ∈ Submodule.torsionBy ℤ M ((ℓ ^ c : ℕ) : ℤ), σ • m = m)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hℓA : IsUnit ((ℓ : ℕ) : ↥A))
    {σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ} (hσF : ∀ x ∈ F, σ x = x)
    (hσ : σ ∈ A.inertiaSubgroupIn ↥K)
    (n : ℕ) (m : M) (hm : m ∈ Submodule.torsionBy ℤ M ((ℓ ^ n : ℕ) : ℤ)) : σ • m = m := by sorry
