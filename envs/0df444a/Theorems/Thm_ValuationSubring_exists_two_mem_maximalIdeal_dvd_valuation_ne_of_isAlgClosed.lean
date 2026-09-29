-- Prove2me | Theorems.Thm_ValuationSubring_exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed
-- name    : ValuationSubring.exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/d3dc2a10-df32-58f6-b4b6-651d1f3411bd
-- title:
--   Two divisors of m in 𝔪 with distinct values
-- statement:
--   Let $L$ be an algebraically closed field and let $A$ be a valuation subring of $L$, with maximal ideal $\mathfrak m$ of $A$ and canonical valuation $v =$ `A.valuation` on $L$. Let $m$ be an element of $A$ lying in $\mathfrak m$ whose image in $L$ is nonzero. The assertion is that there exist $c_1, c_2 \in A$ such that: both $c_1$ and $c_2$ lie in $\mathfrak m$; both are nonzero as elements of $L$; there is $m_1 \in \mathfrak m$ with $m = c_1 m_1$ in $L$, and there is $m_2 \in \mathfrak m$ with $m = c_2 m_2$ in $L$; and $v(c_1) \neq v(c_2)$. Thus $m$ admits two factorisations in which both factors lie in the maximal ideal, with the first factors taking distinct values; note that the divisibility conditions are stated as equalities in $L$, the witnesses $m_1, m_2$ being elements of $A$ belonging to $\mathfrak m$.
--
--   The statement records the divisibility of the value group of a valuation on an algebraically closed field in the concrete form needed for annulus constructions: between $v(m)$ and $1$ there are at least two admissible radii. It is used in the supersingular prolongation arguments for modular curves of full level, in the three lemmas producing a pair of annuli from a node presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (m : ↥A) (hm : m ∈ maximalIdeal ↥A) (hm0 : (m : L) ≠ 0) :
    ∃ c₁ c₂ : ↥A, c₁ ∈ maximalIdeal ↥A ∧ c₂ ∈ maximalIdeal ↥A ∧ (c₁ : L) ≠ 0 ∧ (c₂ : L) ≠ 0 ∧
      (∃ m₁ ∈ maximalIdeal ↥A, (m : L) = c₁ * m₁) ∧ (∃ m₂ ∈ maximalIdeal ↥A, (m : L) = c₂ * m₂) ∧
      A.valuation (c₁ : L) ≠ A.valuation (c₂ : L) := by sorry
