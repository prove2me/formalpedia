-- Prove2me | Theorems.Thm_ValuationSubring_isAlgClosed_residueField
-- name    : ValuationSubring.isAlgClosed_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/09e03244-7f57-5dcf-92a7-00db9f1b269e
-- title:
--   The residue field of a valuation subring of an algebraically closed field
-- statement:
--   Let $K$ be a field that is algebraically closed, and let $A$ be a valuation subring of $K$, i.e. a subring of $K$ such that for every $x \in K$ either $x \in A$ or $x^{-1} \in A$. Such a ring is local, and the assertion is that its residue field $A/\mathfrak{m}_A$, formed as `IsLocalRing.ResidueField A`, is again algebraically closed: every non-constant polynomial over $A/\mathfrak{m}_A$ has a root there. No further hypotheses on $K$ or $A$ are imposed; in particular $A$ may be $K$ itself or any valuation subring of arbitrary rank.
--
--   This is the standard fact that residue fields of valuation rings of algebraically closed fields are algebraically closed; for a place of $\overline{\mathbb{Q}}$ above a rational prime $q$ it gives that the residue field is an algebraic closure of $\mathbb{F}_q$. It is used throughout the reduction theory of curves in this development, where geometric points and tangent cones at singular points of reduced Weierstrass models are required to be rational over the residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isAlgClosed_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.isAlgClosed_residueField {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) : IsAlgClosed (IsLocalRing.ResidueField A) := by sorry
