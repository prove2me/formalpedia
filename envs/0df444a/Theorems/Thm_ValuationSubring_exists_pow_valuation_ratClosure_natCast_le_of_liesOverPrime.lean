-- Prove2me | Theorems.Thm_ValuationSubring_exists_pow_valuation_ratClosure_natCast_le_of_liesOverPrime
-- name    : ValuationSubring.exists_pow_valuation_ratClosure_natCast_le_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/43028952-fe57-51ea-893d-cca4c0275ade
-- title:
--   Powers of v(r) are coinitial in the value group
-- statement:
--   Let $r$ be a prime natural number and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ (the Mathlib algebraic closure `AlgebraicClosure ℚ`), and assume `A.LiesOverPrime r`, i.e. the image of $r$ in $\overline{\mathbb{Q}}$ lies in `A.nonunits`, the set of non-units of $A$. Write $C_A$ for the completion `A.valuation.Completion` of $\overline{\mathbb{Q}}$ with respect to the valuation attached to $A$, carrying its canonical valued structure with values in the value group `A.ValueGroup`, and let `ratClosure A` be the subfield of $C_A$ obtained as the topological closure of the smallest subfield $\bot$ of $C_A$. The natural number $r$, viewed in $C_A$, belongs to this subfield, so it defines an element of `ratClosure A`, and its image under the structure map `algebraMap (ratClosure A) C_A` has a valuation in `A.ValueGroup`. The assertion is that for every $\varepsilon$ in `A.ValueGroup` with $\varepsilon \neq 0$ there exists a natural number $N$ such that $v(r)^{N} \le \varepsilon$; that is, the powers of $v(r)$ are coinitial among the non-zero elements of the value group.
--
--   This is the statement that the valuation of $\overline{\mathbb{Q}}$ at a place above $r$ has rank one, phrased as a supply of arbitrarily small elements of the value group measured in powers of $v(r)$. It is used in the construction of Mumford-type quotients in the Čerednik–Drinfel'd setting, where such powers serve as the scale against which theta-multipliers and torus points are estimated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_pow_valuation_ratClosure_natCast_le_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ValuationSubring

theorem ValuationSubring.exists_pow_valuation_ratClosure_natCast_le_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∀ ε : A.ValueGroup, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap (↥(ratClosure A)) A.valuation.Completion ⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩) ^ N ≤ ε := by sorry
