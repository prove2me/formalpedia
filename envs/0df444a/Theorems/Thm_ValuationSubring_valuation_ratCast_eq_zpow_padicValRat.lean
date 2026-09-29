-- Prove2me | Theorems.Thm_ValuationSubring_valuation_ratCast_eq_zpow_padicValRat
-- name    : ValuationSubring.valuation_ratCast_eq_zpow_padicValRat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/4c5b06a5-b9e8-55ab-95d8-1fc1873db498
-- title:
--   Valuation of a rational in terms of v_q
-- statement:
--   Let $K$ be a field of characteristic zero and let $A$ be a valuation subring of $K$, with associated valuation $v_A =$ `A.valuation` taking values in the multiplicative value group with zero attached to $A$. Let $q$ be a prime natural number, and suppose that the image of $q$ in $K$ satisfies $v_A(q) < 1$, i.e. $q$ lies in the maximal ideal of $A$. Let $r$ be a nonzero rational number. Then the value of the image of $r$ in $K$ is the integral power $$v_A(r) = v_A(q)^{\,\mathrm{padicValRat}\,q\,r},$$ the exponent being the $q$-adic valuation of $r$ as an integer, and the power being taken in the group of units of the value monoid (legitimate since $v_A(q) \neq 0$, as $q$ is nonzero in $K$). Thus the valuation of $A$, restricted to the rationals inside $K$, is determined on $\mathbb{Q}^{\times}$ by the single value $v_A(q)$ together with the $q$-adic valuation.
--
--   This is the statement that any valuation of a characteristic-zero field whose valuation subring lies over $q$ restricts on $\mathbb{Q}^{\times}$ to a power of the $q$-adic valuation. It is used to derive the criteria [`ValuationSubring.ratCast_mem_iff_padicValRat_nonneg`](thm.html#ValuationSubring.ratCast_mem_iff_padicValRat_nonneg) and [`ValuationSubring.valuation_ratCast_eq_one_iff_padicValRat_eq_zero`](thm.html#ValuationSubring.valuation_ratCast_eq_one_iff_padicValRat_eq_zero), which identify membership in $A$ and in $A^{\times}$ with the sign conditions $v_q(r) \ge 0$ and $v_q(r) = 0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_valuation_ratCast_eq_zpow_padicValRat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.valuation_ratCast_eq_zpow_padicValRat {K : Type*} [Field K] [CharZero K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {r : ℚ} (hr : r ≠ 0) : A.valuation (r : K) = A.valuation (q : K) ^ padicValRat q r := by sorry
