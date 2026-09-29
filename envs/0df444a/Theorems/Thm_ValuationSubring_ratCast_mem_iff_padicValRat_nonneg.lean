-- Prove2me | Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
-- name    : ValuationSubring.ratCast_mem_iff_padicValRat_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/9c4919ae-fe96-560a-9e0b-654ad8667de0
-- title:
--   Rational numbers in a valuation subring above q
-- statement:
--   Let $K$ be a field of characteristic zero and let $A$ be a valuation subring of $K$, with associated valuation $A.\mathrm{valuation}$ taking values in the value group-with-zero of $A$. Let $q$ be a prime natural number, and assume that the image of $q$ in $K$ has valuation strictly less than $1$, i.e. $A$ lies over the place $q$ in the sense that $q$ belongs to the maximal ideal of $A$. Let $r$ be a nonzero rational number. Then the image of $r$ under the canonical ring map $\mathbb{Q} \to K$ lies in $A$ if and only if the $q$-adic valuation $\mathrm{padicValRat}\ q\ r \in \mathbb{Z}$ is nonnegative. Thus membership of a nonzero rational in $A$ is governed entirely by its $q$-adic integrality; no hypothesis beyond $v_A(q) < 1$ relating $A$ to $q$ is required.
--
--   This is the statement that a valuation subring of a characteristic-zero field lying over the rational prime $q$ induces on $\mathbb{Q}$ exactly the $q$-adic valuation ring, so that $A \cap \mathbb{Q} = \mathbb{Z}_{(q)}$ on nonzero elements. It is used throughout the work with integral models and integrality of coordinates on modular curves, where rational constants must be recognised as members of a local ring above $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.ratCast_mem_iff_padicValRat_nonneg {K : Type*} [Field K] [CharZero K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {r : ℚ} (hr : r ≠ 0) : (r : K) ∈ A ↔ 0 ≤ padicValRat q r := by sorry
