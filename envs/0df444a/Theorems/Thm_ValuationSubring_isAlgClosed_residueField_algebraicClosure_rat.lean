-- Prove2me | Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
-- name    : ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/eb4c18b6-e1f2-5295-80a5-3006943cc16a
-- title:
--   Residue fields of valuation rings of ℚ̄ are algebraically closed
-- statement:
--   Let $A$ be a valuation subring of the field $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, i.e. a subring of $\overline{\mathbb Q}$ that is a valuation ring with fraction field $\overline{\mathbb Q}$. The theorem asserts that the residue field of $A$, namely the quotient of $A$ by its unique maximal ideal, is algebraically closed: every nonconstant polynomial over it has a root, equivalently it admits no proper algebraic extension. No further hypotheses are imposed; the result holds for an arbitrary valuation subring of $\overline{\mathbb Q}$, including $\overline{\mathbb Q}$ itself (whose residue field is $\overline{\mathbb Q}$) and the valuation rings associated with the places of $\overline{\mathbb Q}$ above a rational prime, whose residue fields are then $\overline{\mathbb F_p}$. The statement is specialised to the base field $\overline{\mathbb Q}$, although the same argument applies over any algebraically closed field.
--
--   This is the standard fact that a valuation ring whose fraction field is algebraically closed has algebraically closed residue field. It is used throughout the formalisation whenever a place of $\overline{\mathbb Q}$ is chosen and one needs the residue field at that place to be algebraically closed, for instance in producing closed fibres and reductions of curves and in the local analysis of Galois representations at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing

theorem ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    IsAlgClosed (ResidueField A) := by sorry
