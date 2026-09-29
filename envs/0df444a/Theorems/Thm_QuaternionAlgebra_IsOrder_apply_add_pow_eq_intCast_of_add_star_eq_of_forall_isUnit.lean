-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_apply_add_pow_eq_intCast_of_add_star_eq_of_forall_isUnit
-- name    : QuaternionAlgebra.IsOrder.apply_add_pow_eq_intCast_of_add_star_eq_of_forall_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/9645f37f-6ccf-5ab0-991c-bf3e6b95bcd9
-- title:
--   Reduced trace and χ+χ^q at a ramified prime
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $B=\mathbb{H}[\mathbb{Q},a,b]$ be the associated rational quaternion algebra, and let $q$ be a prime. Assume that for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ whose ideal contains $q$, every non-zero element of $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$, with $\mathbb{Q}_v$ the $v$-adic completion, is a unit; that is, $B$ is ramified at $q$. Let $O\subseteq B$ be a $\mathbb{Z}$-submodule which is an order in the sense of the project's predicate [`QuaternionAlgebra.IsOrder`](def/QuaternionAlgebra_Order.html#L11): it contains $1$, is closed under multiplication, its $\mathbb{Q}$-span is all of $B$, and it is finitely generated over $\mathbb{Z}$. Let $F$ be a field of characteristic $q$ and $\chi:O\to F$ any function (no ring-map structure is assumed) such that $\chi(1)=1$, $\chi(x+y)=\chi(x)+\chi(y)$ for all $x,y\in O$, and $\chi(xy)=\chi(x)\chi(y)$ whenever $x,y\in O$ and the product $xy$, formed in $B$, lies in $O$. Then for every $x\in O$ and every integer $n$ with $x+\bar{x}=n$ in $B$, where $\bar{\;}$ is quaternion conjugation, so that $n$ is the reduced trace of $x$, one has $\chi(x)+\chi(x)^q=n\cdot 1_F$ in $F$.
--
--   This is the statement that at a prime $q$ at which a rational quaternion algebra ramifies, any unital additive and multiplicative map from an order to a field of characteristic $q$ lands in a quadratic extension of $\mathbb{F}_q$ on which the reduced trace reduces to the trace of $\mathbb{F}_{q^2}/\mathbb{F}_q$; the proof uses only the integrality of reduced traces and norms on an order, so no maximality of $O$ is required. It feeds into [`QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt), where orders in indefinite quaternion algebras ramified at a prescribed set of primes are compared with matrix algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_apply_add_pow_eq_intCast_of_add_star_eq_of_forall_isUnit.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Quaternion QuaternionAlgebra IsDedekindDomain NumberField
open scoped TensorProduct

theorem QuaternionAlgebra.IsOrder.apply_add_pow_eq_intCast_of_add_star_eq_of_forall_isUnit
    {a b : ℚ} (q : ℕ) [Fact q.Prime]
    (hq : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    (O : Submodule ℤ ℍ[ℚ, a, b]) (hO : QuaternionAlgebra.IsOrder O)
    (F : Type*) [Field F] [CharP F q] (χ : ↥O → F)
    (h1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ O, χ ⟨1, h⟩ = 1)
    (hadd : ∀ x y : ↥O, χ (x + y) = χ x + χ y)
    (hmul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ O),
      χ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = χ x * χ y)
    (x : ↥O) (n : ℤ) (hn : (x : ℍ[ℚ, a, b]) + star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) :
    χ x + χ x ^ q = (n : F) := by sorry
