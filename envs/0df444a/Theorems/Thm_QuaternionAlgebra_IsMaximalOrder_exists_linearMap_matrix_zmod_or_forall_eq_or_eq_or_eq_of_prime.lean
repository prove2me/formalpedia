-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/9779ae62-fe87-58b8-8011-9336f7a3c4b3
-- title:
--   Maximal order modulo ℓ: split or ramified alternative
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order, i.e. $\Lambda$ contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$ and is finitely generated as a $\mathbb{Z}$-module, and every order containing $\Lambda$ equals $\Lambda$; let $\ell$ be a prime. Then at least one of the following holds. (i) There is a $\mathbb{Z}$-linear map $\varphi:\Lambda\to M_2(\mathbb{Z}/\ell)$ which sends $1$ to $1$ (the conclusion being stated for each proof that $1\in\Lambda$), satisfies $\varphi(xy)=\varphi(x)\varphi(y)$ for all $x,y\in\Lambda$ (again stated for each proof that the product $xy$ lies in $\Lambda$), is surjective, and has $\varphi(x)=0$ exactly when $x=\ell y$ in $\mathbb{H}[\mathbb{Q},a,b]$ for some $y\in\Lambda$. (ii) Both: every $\mathbb{Z}$-submodule $J$ of $\mathbb{H}[\mathbb{Q},a,b]$ with $xy\in J$ for all $x\in\Lambda$, $y\in J$, with $\operatorname{span}_{\mathbb{Z}}(\ell\cdot\Lambda)\le J\le\Lambda$, is either $\operatorname{span}_{\mathbb{Z}}(\ell\cdot\Lambda)$, or has underlying set $\{x\in\Lambda:\operatorname{nrd}x=\ell n\text{ for some }n\in\mathbb{Z}\}$, or is $\Lambda$; and there exists $x\in\Lambda$ whose reduced norm $\operatorname{nrd}x=x_{0}^{2}-ax_{1}^{2}-bx_{2}^{2}+abx_{3}^{2}$ is $\ell$ times an integer but not $\ell^{2}$ times an integer. Thus the unitality and multiplicativity in (i) are phrased as conditional statements on membership rather than as $\varphi$ being a ring homomorphism, and the dichotomy is an inclusive disjunction.
--
--   This is the local structure theory of a maximal order in a rational quaternion algebra at a single prime $\ell$, stated without completions and with no hypothesis on the ramification of the algebra: either $\Lambda/\ell\Lambda\cong M_2(\mathbb{F}_\ell)$ (split case), or the $\Lambda$-stable lattices between $\ell\Lambda$ and $\Lambda$ are only $\ell\Lambda$, the set of elements of reduced norm divisible by $\ell$, and $\Lambda$, together with an element of reduced norm exactly divisible by $\ell$ (ramified case). It is used by [`QuaternionAlgebra.IsMaximalOrder.exists_mul_mem_line_of_line_of_prime`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_mul_mem_line_of_line_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (ℓ : ℕ) [Fact ℓ.Prime] :
    (∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧
      Function.Surjective φ ∧
      (∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))) ∨
    ((∀ J : Submodule ℤ ℍ[ℚ, a, b], (∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J) →
        Submodule.span ℤ ((ℓ : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ≤ J → J ≤ Λ →
          J = Submodule.span ℤ ((ℓ : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ∨
            (J : Set ℍ[ℚ, a, b]) = {x | x ∈ Λ ∧ ∃ n : ℤ, nrd x = (ℓ : ℚ) * n} ∨ J = Λ) ∧
      (∃ x ∈ Λ, (∃ n : ℤ, nrd x = (ℓ : ℚ) * n) ∧ ¬ (∃ n : ℤ, nrd x = (ℓ : ℚ) ^ 2 * n))) := by sorry
