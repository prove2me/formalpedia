-- Prove2me | Theorems.Thm_QuaternionAlgebra_isMaximalOrder_of_forall_prime_ne_of_range_eq
-- name    : QuaternionAlgebra.isMaximalOrder_of_forall_prime_ne_of_range_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/5c093b3e-63c1-5640-b4c7-7a4547431e0d
-- title:
--   Maximality of an order split away from p and p-saturated
-- statement:
--   Fix a prime $p$ and a ring $O$ which is free and finite as a $\mathbb{Z}$-module. Assume two hypotheses on $O$: first, for every prime $\ell \neq p$ there exists an isomorphism of $\mathbb{Z}_\ell$-algebras $\mathbb{Z}_\ell \otimes_{\mathbb{Z}} O \cong M_2(\mathbb{Z}_\ell)$; second, $O$ is $p$-saturated for integral elements, in the sense that any $x \in O$ satisfying a relation $x^2 - t\cdot x + n\cdot 1 = 0$ with integers $t, n$ such that $p \mid t$ and $p^2 \mid n$ lies in $p\,O$, i.e. $x = p\cdot y$ for some $y \in O$. Fix rationals $a, b$ and an injective ring homomorphism $\theta : O \to \mathbb{H}[\mathbb{Q}, a, b]$ into the quaternion algebra $\left(\frac{a,b}{\mathbb{Q}}\right)$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q}, a, b]$ which is an order, that is: $1 \in \Lambda$, $\Lambda$ is closed under multiplication, the $\mathbb{Q}$-span of $\Lambda$ is the whole algebra, and $\Lambda$ is finitely generated over $\mathbb{Z}$; and assume the image of $\theta$ is exactly $\Lambda$ as a subset. The conclusion is that $\Lambda$ is a maximal order: it is an order, and every order $\Lambda'$ of $\mathbb{H}[\mathbb{Q}, a, b]$ with $\Lambda \le \Lambda'$ equals $\Lambda$.
--
--   This is the maximality step in the construction of maximal orders in a definite quaternion algebra ramified at a prescribed set of places: local splitting data away from $p$ together with $p$-saturation of integral elements forces an abstract order to admit no proper over-order. It is used by [`QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne`](thm.html#QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne); the argument passes through the integrality of the reduced trace and reduced norm on orders, via [`QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd`](thm.html#QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd) and the characteristic identity [`QuaternionAlgebra.sq_sub_trd_mul_add_nrd`](thm.html#QuaternionAlgebra.sq_sub_trd_mul_add_nrd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_isMaximalOrder_of_forall_prime_ne_of_range_eq.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.isMaximalOrder_of_forall_prime_ne_of_range_eq
    (p : ℕ) [Fact p.Prime] (O : Type*) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O]
    (hsplit : ∀ ℓ : ℕ, [Fact ℓ.Prime] → ℓ ≠ p →
      Nonempty (ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]))
    (hmaxp : ∀ x : O, (∃ t n : ℤ, x * x - t • x + n • (1 : O) = 0 ∧ (p : ℤ) ∣ t ∧ (p : ℤ) ^ 2 ∣ n) →
      ∃ y : O, x = (p : ℤ) • y)
    {a b : ℚ} (θ : O →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) :
    QuaternionAlgebra.IsMaximalOrder Λ := by sorry
