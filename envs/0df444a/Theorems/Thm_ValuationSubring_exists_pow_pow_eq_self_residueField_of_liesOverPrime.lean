-- Prove2me | Theorems.Thm_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime
-- name    : ValuationSubring.exists_pow_pow_eq_self_residueField_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/432f7247-4f5d-5d36-9f36-296303bcd897
-- title:
--   Residue field of a place of ℚ̄ above q is algebraic over mathbb F_q
-- statement:
--   Let $A$ be a valuation subring of a fixed algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$, let $q$ be a prime natural number, and assume that $A$ lies over $q$ in the sense of the project predicate [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), i.e. that the image of $q$ in $\overline{\mathbb Q}$ belongs to `A.nonunits`, the set of non-invertible elements of $A$ (equivalently, $q$ lies in the maximal ideal of the local ring $A$). Let $a$ be an arbitrary element of the residue field $\kappa(A)$ of $A$, formed as `IsLocalRing.ResidueField A`. The assertion is that there exists a natural number $r$ with $0 < r$ such that $a^{q^{r}} = a$. Thus every element of $\kappa(A)$ is fixed by some positive power of the $q$-power Frobenius; this is the elementwise form of the statement that $\kappa(A)$ is an algebraic extension of $\mathbb F_q$ (no uniform $r$ is claimed, and no statement about algebraic closedness of $\kappa(A)$ is made here).
--
--   This is the standard fact that the residue field of a place of $\overline{\mathbb Q}$ above a prime $q$ is algebraic over $\mathbb F_q$, recorded in the Frobenius-fixed-point form that is convenient downstream. It is used in the study of reduction of modular curves and of Tate curves at a place above $q$, for instance in the statements about semistable models and Igusa inertia and in the congruence statements for $q$-expansion coefficients of normalised eigenforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_pow_pow_eq_self_residueField_of_liesOverPrime
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q)
    (a : IsLocalRing.ResidueField A) :
    ∃ r : ℕ, 0 < r ∧ a ^ q ^ r = a := by sorry
