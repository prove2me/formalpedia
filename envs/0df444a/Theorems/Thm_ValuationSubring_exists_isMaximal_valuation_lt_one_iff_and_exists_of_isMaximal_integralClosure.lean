-- Prove2me | Theorems.Thm_ValuationSubring_exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
-- name    : ValuationSubring.exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/599bca2d-9b5d-5a3b-869a-d3e4c13be9a3
-- title:
--   Valuation rings over O versus maximal ideals of the integral closure
-- statement:
--   Let $E$ and $F$ be fields with $F$ an $E$-algebra, and let $O$ be a valuation subring of $E$; write $B =$ `integralClosure O F` for the integral closure of $O$ in $F$, taken with respect to the algebra structure on $F$ over the subring $O$ of $E$. Say that a valuation subring $O'$ of $F$ lies over $O$ when, for every $x \in E$, the image $\mathrm{algebraMap}\,E\,F\,x$ lies in $O'$ if and only if $x$ lies in $O$. The theorem asserts the conjunction of two statements. First, for every valuation subring $O'$ of $F$ lying over $O$ there is a maximal ideal $M$ of $B$ such that every $b \in B$ satisfies $O'.\mathrm{valuation}(b) \le 1$, and satisfies $O'.\mathrm{valuation}(b) < 1$ precisely when $b \in M$; thus $B \subseteq O'$ and the centre of $O'$ on $B$ (the contraction of the maximal ideal of $O'$) is the maximal ideal $M$. Second, conversely, for every maximal ideal $M$ of $B$ there is a valuation subring $O'$ of $F$ lying over $O$ with the same two properties for all $b \in B$, i.e. whose centre on $B$ is $M$. No algebraicity or finiteness assumption on $F$ over $E$ is imposed.
--
--   This is the classical correspondence between the valuation rings of an extension field lying over a given valuation ring and the maximal ideals of the integral closure, one direction resting on the integral closedness of valuation rings and the other on Chevalley's extension theorem. It underlies the results on the transitive action of the Galois group on the valuation rings above $O$ and on the associated residue field extension, namely [`ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois`](thm.html#ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois), [`ValuationSubring.exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois`](thm.html#ValuationSubring.exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois) and [`ValuationSubring.normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois`](thm.html#ValuationSubring.normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure.lean

import Mathlib.RingTheory.Valuation.ValuationSubring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    (O : ValuationSubring E) :
    (∀ O' : ValuationSubring F, (∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) →
      ∃ M : Ideal (integralClosure O F), M.IsMaximal ∧
        ∀ b : integralClosure O F, O'.valuation (b : F) ≤ 1 ∧ (O'.valuation (b : F) < 1 ↔ b ∈ M)) ∧
    (∀ M : Ideal (integralClosure O F), M.IsMaximal →
      ∃ O' : ValuationSubring F, (∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) ∧
        ∀ b : integralClosure O F, O'.valuation (b : F) ≤ 1 ∧ (O'.valuation (b : F) < 1 ↔ b ∈ M)) := by sorry
