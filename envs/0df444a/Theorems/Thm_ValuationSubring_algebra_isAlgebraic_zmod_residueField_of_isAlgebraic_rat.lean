-- Prove2me | Theorems.Thm_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat
-- name    : ValuationSubring.algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/0ac8a2a3-eabc-5d90-aafe-1e1be57ea15c
-- title:
--   Residue field of a valuation subring is algebraic over mathbb Fₚ
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure making $K$ algebraic over $\mathbb{Q}$, let $A \subseteq K$ be a valuation subring, and let $p$ be a prime number. Assume moreover that the residue field $\mathrm{ResidueField}(A)$ of $A$ as a local ring is endowed with a $\mathbb{Z}/p$-algebra structure (any such structure; it is not constructed but hypothesised, and expresses that $A$ lies over $p$). Then $\mathrm{ResidueField}(A)$ is algebraic over $\mathbb{Z}/p$ in the sense of `Algebra.IsAlgebraic`: every element of the residue field is a root of some non-zero polynomial with coefficients in $\mathbb{Z}/p$, the coefficients being transported to the residue field along the given algebra map. No completeness, discreteness or rank hypothesis is placed on the valuation, and $K$ is not assumed to be a number field — only algebraic over $\mathbb{Q}$.
--
--   This is the standard fact that a valuation of a field algebraic over $\mathbb{Q}$ whose residue characteristic is $p$ has residue field algebraic over $\mathbb{F}_p$; in particular such a residue field is perfect and, when algebraically closed, is an algebraic closure of $\mathbb{F}_p$. It is used as an input to reduction arguments over residue fields, for instance in the genus computations for modular curves at full level and in the Čerednik–Drinfel'd comparison of degeneracy and Hecke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat
    (K : Type*) [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) (IsLocalRing.ResidueField ↥A)] :
    Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField ↥A) := by sorry
