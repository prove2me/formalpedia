-- Prove2me | Theorems.Thm_ValuationSubring_exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le
-- name    : ValuationSubring.exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/40343309-9baf-5ad8-bca8-b094fcd07f25
-- title:
--   Trace of a valuation ring on a finite layer: finiteness up to units
-- statement:
--   Let $k \subseteq L$ be fields with $k$ of characteristic zero, $L$ a $k$-algebra, and let $A$ be a valuation subring of $L$. Let $K_0 \subseteq K'$ be intermediate fields of $L/k$, each finite-dimensional over $k$. Let $C$ be a subring of $L$ whose elements are exactly those lying in both $A$ and $K_0$, and assume $C$ is a domain and a discrete valuation ring; let $C'$ be a subring of $L$ whose elements are exactly those lying in both $A$ and $K'$. Assume further that $C'$ is not a field in the strong sense that some $t \in C'$ has $t^{-1} \notin C'$. The conclusion is the existence of a finite subset $G \subseteq C'$ of $L$ such that for every $c \in C'$ there are $y, z \in L$, both lying in the $C$-submodule of $L$ spanned by $G$, with $z \in C'$, $z^{-1} \in C'$, $z \neq 0$, and $c z = y$. Thus every element of $C'$ is a quotient $y/z$ of two elements of a fixed finitely generated $C$-submodule of $C'$, with denominator a unit of $C'$.
--
--   The statement expresses the trace $C' = A \cap K'$ of a valuation subring on a finite layer of constants as a localisation, at the units of $C'$, of a finite module over the trace $C = A \cap K_0$ on a smaller layer; it is a Krull–Akizuki-type finiteness assertion in the form needed for base change. It is used in the construction of localised base changes of node rings along finite extensions of the field of constants, where this finiteness keeps Noetherianity after adjoining $C'$ and localising.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le
    {k L : Type*} [Field k] [Field L] [Algebra k L] [CharZero k] (A : ValuationSubring L)
    (K₀ K' : IntermediateField k L) [FiniteDimensional k ↥K₀] [FiniteDimensional k ↥K'] (hK : K₀ ≤ K')
    (C : Subring L) (hCK₀ : ∀ c : L, c ∈ C ↔ c ∈ A ∧ c ∈ K₀) [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (C' : Subring L) (hC'K' : ∀ c : L, c ∈ C' ↔ c ∈ A ∧ c ∈ K')
    (t : L) (htC' : t ∈ C') (htinv : t⁻¹ ∉ C') :
    ∃ G : Finset L, (↑G ⊆ (C' : Set L)) ∧
      ∀ c : L, c ∈ C' → ∃ y z : L, y ∈ Submodule.span ↥C (G : Set L) ∧ z ∈ Submodule.span ↥C (G : Set L) ∧
        z ∈ C' ∧ z⁻¹ ∈ C' ∧ z ≠ 0 ∧ c * z = y := by sorry
