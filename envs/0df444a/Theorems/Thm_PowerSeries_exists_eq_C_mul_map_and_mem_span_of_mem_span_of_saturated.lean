-- Prove2me | Theorems.Thm_PowerSeries_exists_eq_C_mul_map_and_mem_span_of_mem_span_of_saturated
-- name    : PowerSeries.exists_eq_C_mul_map_and_mem_span_of_mem_span_of_saturated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/29b530a9-e96b-50be-ac69-4743e78a2fe5
-- title:
--   Primitive integral representatives over a valuation ring
-- statement:
--   Let $L$ be a field and let $A$ be a valuation subring of $L$. Let $N$ be an additive subgroup of the ring $\mathbb{Z}[[X]]$ of formal power series over $\mathbb{Z}$, assumed saturated in the sense that for every integer $n \neq 0$ and every $p \in \mathbb{Z}[[X]]$, membership $n \cdot p \in N$ forces $p \in N$. Let $V \in L[[X]]$ be a power series lying in the $L$-submodule spanned by the image of $N$ under coefficientwise application of the canonical ring homomorphism $\mathbb{Z} \to L$, and assume $V \neq 0$. The assertion is that there exist a scalar $c \in L$ and a power series $u \in A[[X]]$ with: $c \neq 0$; $V$ equals the constant series $c$ times the image of $u$ under the coefficientwise inclusion $A \hookrightarrow L$; the coefficientwise reduction of $u$ along the residue map of the local ring $A$ is nonzero in $(A/\mathfrak{m}_A)[[X]]$; and $u$ itself lies in the $A$-submodule of $A[[X]]$ spanned by the image of $N$ under coefficientwise application of $\mathbb{Z} \to A$.
--
--   This is the normalisation step for lattices of integral $q$-series: a nonzero element of the $L$-span of a saturated subgroup $N \subseteq \mathbb{Z}[[X]]$ can be scaled by a single constant so as to become a primitive element of the $A$-span of $N$, i.e. an $A$-combination of elements of $N$ whose reduction modulo the maximal ideal of $A$ does not vanish. It is used in the comparison of $q$-expansion coefficients of modular forms modulo the maximal ideal of a valuation ring, where the conclusion that $u$ lies in the $A$-span of $N$ (and not merely that $u$ is integral with nonzero reduction) is what is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_exists_eq_C_mul_map_and_mem_span_of_mem_span_of_saturated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PowerSeries.exists_eq_C_mul_map_and_mem_span_of_mem_span_of_saturated
    {L : Type*} [Field L] (A : ValuationSubring L)
    (N : AddSubgroup (PowerSeries ℤ))
    (hN : ∀ (n : ℤ) (p : PowerSeries ℤ), n ≠ 0 → n • p ∈ N → p ∈ N)
    {V : PowerSeries L}
    (hV : V ∈ Submodule.span L
      ((fun p : PowerSeries ℤ => p.map (Int.castRingHom L)) '' (N : Set (PowerSeries ℤ))))
    (hV0 : V ≠ 0) :
    ∃ (c : L) (u : PowerSeries A), c ≠ 0 ∧
      V = PowerSeries.C c * u.map (A.subtype : A →+* L) ∧
      u.map (IsLocalRing.residue A) ≠ 0 ∧
      u ∈ Submodule.span A
        ((fun p : PowerSeries ℤ => p.map (Int.castRingHom A)) '' (N : Set (PowerSeries ℤ))) := by sorry
