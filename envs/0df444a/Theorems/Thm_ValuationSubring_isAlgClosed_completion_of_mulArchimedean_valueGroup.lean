-- Prove2me | Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_mulArchimedean_valueGroup
-- name    : ValuationSubring.isAlgClosed_completion_of_mulArchimedean_valueGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/33736742-82aa-5ef7-be4b-96c5e62afa1e
-- title:
--   Completion of an algebraically closed field at a rank-one valuation
-- statement:
--   Let $K$ be a field that is algebraically closed and of characteristic zero, and let $A$ be a valuation subring of $K$ whose value group $A.\mathrm{ValueGroup}$ is multiplicatively archimedean, i.e. for all elements $x$ and $y$ of the value group with $y$ strictly greater than $1$ there is a natural number $n$ with $x \le y^n$. Assume $A \ne \top$, that is, $A$ is a proper subring of $K$, so that the associated valuation $A.\mathrm{valuation}$ on $K$ is nontrivial. Then the completion $A.\mathrm{valuation}.\mathrm{Completion}$ of $K$ with respect to the uniform structure determined by this valuation — a complete valued field carrying the continuous extension of the valuation, into which $K$ embeds with dense image — is again algebraically closed. No rank-one or normed-field structure is assumed in the hypotheses; the archimedean hypothesis on the value group is what makes the valuation equivalent to an absolute value.
--
--   This is Kürschák's theorem: completing an algebraically closed field of characteristic zero at a rank-one place preserves algebraic closedness. It is used in the form [`ValuationSubring.isAlgClosed_completion_of_liesOverPrime`](thm.html#ValuationSubring.isAlgClosed_completion_of_liesOverPrime), which specialises it to valuation subrings lying over a prime and thereby produces complete algebraically closed coefficient fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isAlgClosed_completion_of_mulArchimedean_valueGroup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.isAlgClosed_completion_of_mulArchimedean_valueGroup
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (A : ValuationSubring K) [MulArchimedean A.ValueGroup] (hA : A ≠ ⊤) :
    IsAlgClosed A.valuation.Completion := by sorry
