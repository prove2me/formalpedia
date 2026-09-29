-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/dabf97ca-eae3-54b7-a233-502922f57738
-- title:
--   Conjugating an integral embedding into a special one
-- statement:
--   Let $q,q'$ be natural numbers that are prime, and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order: it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and is maximal for inclusion among submodules with these four properties. Let $c,d\in\mathbb{Q}$ be such that $H=\mathbb{H}[\mathbb{Q},c,d]$ satisfies `IsDefiniteRamifiedExactlyAt c d q`, i.e. $c<0$, $d<0$, and $H\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q\in v$; and let $O\subseteq H$ be a maximal order in the same sense. Finally let $j_0:B\to M_2(H)$ be a $\mathbb{Q}$-algebra homomorphism with all entries of $j_0(m)$ lying in $O$ for every $m\in\Lambda$. Then there exist a $\mathbb{Q}$-algebra homomorphism $j:B\to M_2(H)$ and matrices $\gamma,\gamma'\in M_2(H)$ with $\gamma\gamma'=\gamma'\gamma=1$ such that $j(x)=\gamma' j_0(x)\gamma$ for all $x\in B$, such that all entries of $j(m)$ lie in $O$ for $m\in\Lambda$, and such that, with $hj$ denoting this integrality witness, for every field $F$ in `Type` of characteristic $q$ and every map $\chi:O\to F$ sending $1$ to $1$, additive, and multiplicative (for all $x,y\in O$ and any witness that $xy\in O$), and for every $m\in\Lambda$ and every $n\in\mathbb{Z}$ with $m+\bar m=n$ in $B$, one has $\chi(j(m)_{00})+\chi(j(m)_{11})=n$ in $F$.
--
--   This is the passage from an arbitrary $\Lambda$-integral embedding $B\hookrightarrow M_2(H)$ to one satisfying Drinfeld's special condition at $q$: the reduced diagonal trace of $j(m)$, computed through any unital ring-homomorphic $\chi$ into a field of characteristic $q$, agrees with the reduced trace $m+\bar m$ of $m$. Combined with the existence of integral embeddings it yields the normalised form of the statement used in the Čerednik–Drinfeld uniformisation of Shimura curves, and it is cited by [`QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt) and by [`QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct
open QuaternionAlgebra IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {c d : ℚ} (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    (j₀ : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    (hj₀ : ∀ m ∈ Λ, ∀ i l : Fin 2, j₀ m i l ∈ O) :
    ∃ (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (γ γ' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]),
      γ * γ' = 1 ∧ γ' * γ = 1 ∧ (∀ x : ℍ[ℚ, a, b], j x = γ' * j₀ x * γ) ∧
      ∃ (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O),
      ∀ (F : Type) [Field F] [CharP F q] (χ : ↥O → F),
        (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, χ ⟨1, h⟩ = 1) →
        (∀ x y : ↥O, χ (x + y) = χ x + χ y) →
        (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
          χ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = χ x * χ y) →
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          χ ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩ + χ ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩ = (n : F) := by sorry
