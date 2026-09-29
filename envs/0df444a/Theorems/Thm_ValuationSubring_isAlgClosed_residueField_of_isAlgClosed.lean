-- Prove2me | Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
-- name    : ValuationSubring.isAlgClosed_residueField_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/4017c594-2b02-51a1-a146-fb8ffdf43009
-- title:
--   Residue field of a valuation subring of an algebraically closed field
-- statement:
--   Let $L$ be a field which is algebraically closed, and let $A$ be a valuation subring of $L$, i.e. a subring that is a valuation ring with fraction field $L$ in the sense of Mathlib's `ValuationSubring`. Since $A$ is a local ring, it has a residue field `IsLocalRing.ResidueField A`, the quotient of $A$ by its maximal ideal. The theorem asserts that this residue field is again algebraically closed: every non-constant polynomial with coefficients in $A/\mathfrak m$ has a root in $A/\mathfrak m$. No further hypotheses are imposed on $L$ or on $A$; in particular no assumption is made on the characteristic, the value group, or the rank of $A$, and the case $A = L$ (with trivial maximal ideal) is included.
--
--   This is the standard fact that passing to the residue field of a valuation ring preserves algebraic closedness; it is used, for instance, to identify the residue field of a place of $\overline{\mathbb Q}$ above $p$ with an algebraic closure of $\mathbb F_p$, the field over which geometric special fibres of models over $\mathbb Z_{(p)}$ are read. It is invoked widely in the curve- and model-theoretic parts of the development, for example in the analysis of annuli and semistable coverings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.isAlgClosed_residueField_of_isAlgClosed
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) :
    IsAlgClosed (IsLocalRing.ResidueField ↥A) := by sorry
