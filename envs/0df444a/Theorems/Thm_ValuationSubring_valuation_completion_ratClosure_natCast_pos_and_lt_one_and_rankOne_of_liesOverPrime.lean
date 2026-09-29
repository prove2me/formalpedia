-- Prove2me | Theorems.Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
-- name    : ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/e6a712fe-5bda-51df-affa-dfd4b6350172
-- title:
--   Rank one of the completion of ℚ̄ over r
-- statement:
--   Let $r$ be a prime number and let $A$ be a valuation subring of $\mathrm{AlgebraicClosure}\,\mathbb Q$, and assume `A.LiesOverPrime r`, i.e. that the image of $r$ in $\overline{\mathbb Q}$ lies in the nonunits of $A$. Write $C_A$ for the completion `A.valuation.Completion` of $\overline{\mathbb Q}$ with respect to the valuation attached to $A$, with its canonical `Valued` structure and valuation $v$, and let `ratClosure A` be the subfield of $C_A$ obtained as the topological closure of the bottom subfield $\bot$ of $C_A$. The element $r$ of $C_A$ lies in `ratClosure A`, and the assertion is threefold for the image of this element under the algebra map from `ratClosure A` back to $C_A$: first, its valuation is strictly positive; second, its valuation is strictly less than $1$; and third, the valuation of $C_A$ has rank one in the elementwise form that for all $x, y \in C_A$ with $v(x) < 1$ and $y \neq 0$ there exists a natural number $n$ with $v(x)^n \le v(y)$.
--
--   This records that a place of $\overline{\mathbb Q}$ above a prime $r$ yields a complete valued field of rank one in which $r$ is a nonzero topologically nilpotent element of the closure of $\mathbb Q$; such data are what is needed to run rigid-analytic and Mumford-uniformisation arguments over $C_A$. It is used in the construction of period data and theta functions for Mumford quotients in the Picard-group part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ValuationSubring

theorem ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    0 < Valued.v (algebraMap (↥(ratClosure A)) A.valuation.Completion ⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩) ∧
    Valued.v (algebraMap (↥(ratClosure A)) A.valuation.Completion ⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩) < 1 ∧
    (∀ x y : A.valuation.Completion, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y) := by sorry
