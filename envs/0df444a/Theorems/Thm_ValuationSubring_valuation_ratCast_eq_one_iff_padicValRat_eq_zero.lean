-- Prove2me | Theorems.Thm_ValuationSubring_valuation_ratCast_eq_one_iff_padicValRat_eq_zero
-- name    : ValuationSubring.valuation_ratCast_eq_one_iff_padicValRat_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/e50046cd-f1c8-523f-b7d0-6d3e6d17328f
-- title:
--   Valuation of a rational is 1 iff v_q(r)=0
-- statement:
--   Let $K$ be a field of characteristic zero and let $A$ be a valuation subring of $K$, with associated valuation `A.valuation` taking values in the value group with zero of $A$. Let $q$ be a prime natural number, and assume that the image of $q$ in $K$ has valuation strictly less than $1$, i.e. $A.\mathrm{valuation}(q) < 1$, so that the place determined by $A$ lies over $q$. Let $r$ be a nonzero rational number. The theorem asserts the equivalence: the valuation of the image of $r$ in $K$ equals $1$ if and only if the $q$-adic valuation $\mathrm{padicValRat}\ q\ r$ of $r$ is zero. In other words, $r$ is a unit for the valuation attached to $A$ exactly when $r$ is a $q$-adic unit.
--
--   This is the elementary dictionary between a place of a characteristic-zero field lying over the prime $q$ and the $q$-adic valuation on $\mathbb{Q}$, in its "unit" form. It is used throughout the project whenever integrality or unit-ness of a rational number at such a place must be read off from its $q$-adic valuation, for instance in computations of determinants of local units and in the analysis of charts and Hasse exponents on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_valuation_ratCast_eq_one_iff_padicValRat_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.valuation_ratCast_eq_one_iff_padicValRat_eq_zero {K : Type*} [Field K]
    [CharZero K] (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {r : ℚ} (hr : r ≠ 0) : A.valuation (r : K) = 1 ↔ padicValRat q r = 0 := by sorry
