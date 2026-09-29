-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/757f54df-36f2-5ba8-adac-3747bf52f79e
-- title:
--   Special integral embedding of B into M₂(H') with centraliser
-- statement:
--   Let $r$ and $\bar r$ be primes with $\bar r \neq r$. Let $a, b \in \mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q}, a, b]$ is indefinite and ramified exactly at $\{r,\bar r\}$, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $r \in v$ or $\bar r \in v$; let $\Lambda$ be a $\mathbb{Z}$-submodule of it which is a maximal order, that is, $1 \in \Lambda$, $\Lambda$ is closed under multiplication, finitely generated, spans the algebra over $\mathbb{Q}$, and is maximal among such submodules under inclusion. Let $c, d \in \mathbb{Q}$ with $c < 0$, $d < 0$ and $\mathbb{H}[\mathbb{Q},c,d] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ a division algebra exactly for $v$ containing $r$, with $O$ a maximal order in $\mathbb{H}[\mathbb{Q},c,d]$, and let $a_1, b_1 \in \mathbb{Q}$ satisfy the same condition with $\bar r$ in place of $r$. Then there are $\mathbb{Q}$-algebra homomorphisms $j : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{H}[\mathbb{Q},c,d])$ and $\tau : \mathbb{H}[\mathbb{Q},a_1,b_1] \to M_2(\mathbb{H}[\mathbb{Q},c,d])$ such that all entries of $j(m)$ lie in $O$ for $m \in \Lambda$, both $j$ and $\tau$ are injective, a matrix $y$ commutes with $j(m)$ for all $m$ if and only if $y$ lies in the image of $\tau$, and $j$ is special at $r$: for every field $F$ of characteristic $r$ and every map $\chi : O \to F$ with $\chi(1) = 1$, additive, and satisfying $\chi(xy) = \chi(x)\chi(y)$ whenever $x, y, xy \in O$, one has $\chi(j(m)_{00}) + \chi(j(m)_{11}) = n$ in $F$ for every $m \in \Lambda$ and $n \in \mathbb{Z}$ with $m + \bar m = n$.
--
--   This is the input datum for the Čerednik–Drinfeld description of the fake elliptic curves attached to the indefinite quaternion algebra ramified at $\{r,\bar r\}$: an embedding of $B$ into $M_2(H')$ carrying a maximal order into $M_2(O)$, whose reduced trace is computed by any multiplicative additive character of $O$ in characteristic $r$, together with the identification of its centraliser with the definite quaternion algebra ramified exactly at $\bar r$. It is used in the construction of a fake elliptic curve with prescribed formal module and endomorphism dictionary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField CerednikDrinfeld
open QuaternionAlgebra

theorem QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt
    {r rbar : ℕ} [Fact r.Prime] [Fact rbar.Prime] (hrr : rbar ≠ r)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {c d : ℚ} (hH' : IsDefiniteRamifiedExactlyAt c d r)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar) :
    ∃ (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
      (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O),
      Function.Injective j ∧ Function.Injective τ ∧
      (∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ m : ℍ[ℚ, a, b], y * j m = j m * y) ↔ y ∈ Set.range τ) ∧
      ∀ (F : Type) [Field F] [CharP F r] (χ : ↥O → F),
        (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, χ ⟨1, h⟩ = 1) →
        (∀ x y : ↥O, χ (x + y) = χ x + χ y) →
        (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
          χ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = χ x * χ y) →
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          χ ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩ + χ ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩ = (n : F) := by sorry
