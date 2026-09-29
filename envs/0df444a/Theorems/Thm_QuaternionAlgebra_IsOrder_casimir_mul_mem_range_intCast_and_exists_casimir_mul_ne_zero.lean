-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero
-- name    : QuaternionAlgebra.IsOrder.casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/e0658fa6-f1e0-5bfa-8cb8-d2736b238e55
-- title:
--   Casimir elements of a rational quaternion order multiply to integers
-- statement:
--   Let $a,b\in\mathbb{Q}$ be non-zero and let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the project's predicate `IsOrder`, i.e. $1\in\Lambda$, $\Lambda$ is closed under multiplication, the $\mathbb{Q}$-span of $\Lambda$ is all of $\mathbb{H}[\mathbb{Q},a,b]$, and $\Lambda$ is finitely generated as a $\mathbb{Z}$-module. Let $R$ be a ring (in an arbitrary universe) together with an injective ring homomorphism $\theta\colon R\to\mathbb{H}[\mathbb{Q},a,b]$ whose range, as a set, is exactly $\Lambda$; thus $R$ is an abstract copy of the ring structure carried by the lattice $\Lambda$. Call $c\in R\otimes_{\mathbb{Z}}R$ a Casimir element if $(x\otimes 1)\,c=c\,(1\otimes x)$ for all $x\in R$, the products being taken in the ring $R\otimes_{\mathbb{Z}}R$. The conclusion is a conjunction: first, for every Casimir element $c$ there is an integer $n$ with $\mathrm{mul}'(c)=(n:R)$, where $\mathrm{mul}'$ denotes the multiplication map `LinearMap.mul' ℤ R` sending $\sum_i u_i\otimes v_i$ to $\sum_i u_iv_i$; second, there exists a Casimir element $c$ with $\mathrm{mul}'(c)\neq 0$.
--
--   This is the separability-type input for orders in rational quaternion algebras: the image under multiplication of the Casimir elements of $\Lambda\otimes_{\mathbb{Z}}\Lambda^{\mathrm{op}}$ lies in the centre $\mathbb{Z}\cdot 1$ and is non-zero, the non-zero value being produced from the reduced-trace form. It is used in the construction of a separability element for a maximal order that is indefinite and ramified exactly at a prescribed set, via [`QuaternionAlgebra.IsMaximalOrder.exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open QuaternionAlgebra

universe v

theorem QuaternionAlgebra.IsOrder.casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    {R : Type v} [Ring R] (θ : R →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) :
    (∀ c : R ⊗[ℤ] R, (∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c = c * ((1 : R) ⊗ₜ[ℤ] x)) →
        ∃ n : ℤ, LinearMap.mul' ℤ R c = (n : R)) ∧
    ∃ c : R ⊗[ℤ] R, (∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c = c * ((1 : R) ⊗ₜ[ℤ] x)) ∧
      LinearMap.mul' ℤ R c ≠ 0 := by sorry
