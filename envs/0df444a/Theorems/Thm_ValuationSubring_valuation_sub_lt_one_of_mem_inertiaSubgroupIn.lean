-- Prove2me | Theorems.Thm_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn
-- name    : ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/208713d0-dc9c-5a20-906e-0c04d855d9ea
-- title:
--   Inertia elements fix valuation ring elements modulo the maximal ideal
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $A$ be a valuation subring of $L$, and let $\sigma$ be a $K$-algebra automorphism of $L$ lying in `A.inertiaSubgroupIn K`, that is, in the image under the inclusion of the decomposition subgroup of $A$ (the stabiliser of $A$ inside $L \simeq_{\text{alg}[K]} L$) of the inertia subgroup of $A$, the kernel of the induced action of that decomposition subgroup on the residue field of the local ring $A$. Let $a$ be an element of $A$. Then the assertion is twofold: first, $\sigma a$ again lies in $A$; second, the valuation attached to $A$ (taking values in the value group $L^\times/A^\times$ with $1$ as the unit) satisfies $A.\mathrm{valuation}(\sigma a - a) < 1$, equivalently $\sigma a - a$ lies in the maximal ideal of $A$. So an inertia element carries $A$ into itself and moves each element of $A$ only within its residue class.
--
--   This is the standard characterisation of the inertia group of a place as those automorphisms preserving the valuation ring and acting trivially modulo the maximal ideal, here in the form of an explicit congruence $\sigma a \equiv a$ for $a \in A$. It is the form in which inertia is used downstream in the project, in arguments about ramification of torsion points and of finite flat group schemes, and in the analysis of inertia at $2$ for a Frey package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn {K L : Type*} [Field K]
    [Field L] [Algebra K L] (A : ValuationSubring L) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.inertiaSubgroupIn K) {a : L} (ha : a ∈ A) :
    σ a ∈ A ∧ A.valuation (σ a - a) < 1 := by sorry
