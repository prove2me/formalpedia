-- Prove2me | Theorems.Thm_ValuationSubring_not_countable_upperHalfPlane_ratClosure_completion_of_liesOverPrime
-- name    : ValuationSubring.not_countable_upperHalfPlane_ratClosure_completion_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/fc7a7de3-3be3-57c0-80f3-0c0578ad2d3b
-- title:
--   Uncountability of the r-adic upper half plane over C_A
-- statement:
--   Let $r$ be a prime and let $A$ be a valuation subring of an algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ satisfying `A.LiesOverPrime r`, i.e. the image of $r$ in $\overline{\mathbb Q}$ lies in the non-units of $A$ (so $A$ is a place above $r$). Write $C_A$ for the completion `A.valuation.Completion` of $\overline{\mathbb Q}$ with respect to the valuation attached to $A$, and let `ratClosure A` be the subfield of $C_A$ obtained as the topological closure of the smallest subfield $\bot$ of $C_A$, i.e. the closure of the image of $\mathbb Q$. The assertion is that the set $\Omega =$ `Omega.upperHalfPlane (ratClosure A) C_A`, which by definition is the complement in $C_A$ of the range of the algebra map from `ratClosure A` to $C_A$, that is, the set of elements of $C_A$ not lying in the closure of $\mathbb Q$, is not countable.
--
--   This is the cardinality statement that Drinfeld's $r$-adic upper half plane over $C_A$, taken with respect to the closure of $\mathbb Q$ inside $C_A$, has uncountably many points. It supplies the 'uncountably many points versus a countable group' input used in the Čerednik–Drinfeld part of the project, in the arguments about invariant fields and Mumford quotients that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_not_countable_upperHalfPlane_ratClosure_completion_of_liesOverPrime.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ValuationSubring
open CerednikDrinfeld

theorem ValuationSubring.not_countable_upperHalfPlane_ratClosure_completion_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ¬ (Omega.upperHalfPlane ↥(ratClosure A) A.valuation.Completion).Countable := by sorry
