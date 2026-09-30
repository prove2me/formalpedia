-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_commutative_weighted_surjectivity_iff
-- name    : WeierstrassEllipticZeta.commutative_weighted_surjectivity_iff
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-11T19:55:26.754641+00:00
-- url     : https://prove2.me/theorems/a6f3ab1d-100f-4c67-a8e4-978dc07dac1a
-- title:
--   Weighted surjectivity and units in a commutative monoid
-- statement:
--   Let $M$ be a commutative monoid, let $S$ be any type, let $f:S\to M$ be any map, and let $a\in M$. Then
--   $$
--   \bigl(s\mapsto f(s)a\text{ is surjective}\bigr)
--   \quad\Longleftrightarrow\quad
--   \bigl(f\text{ is surjective and }a\text{ is a unit}\bigr).
--   $$
--   No algebraic structure on $S$ or homomorphism property of $f$ is assumed. The monoid may be trivial; no field or finite-dimensionality hypothesis is needed.
-- source:
--   Derived supporting algebra lemma for the Senthil Kumar mission. For an arbitrary map f from a type into a commutative monoid M, multiplication of f by a fixed element a is surjective iff f itself is surjective and a is a unit. A preimage of 1 makes a a unit, and unit cancellation proves surjectivity of f. Conversely, multiplication by a unit is bijective. At Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, use isUnit_iff_exists_inv' in Algebra/Group/Units/Defs.lean lines 441-443, IsUnit.mul_right_cancel in Algebra/Group/Units/Basic.lean lines 307-309, and IsUnit.isUnit_iff_mulRight_bijective in lines 336-341. Primary documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Units/Basic.html and https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Units/Defs.html . No field, finite-dimensionality, nontriviality, or homomorphism hypothesis is required. Commutativity is assumed. No platform theorem dependencies or new definitions.

import Mathlib.Algebra.Group.Units.Basic

theorem WeierstrassEllipticZeta.commutative_weighted_surjectivity_iff
    (α M : Type*) [CommMonoid M] (f : α → M) (a : M) :
    Function.Surjective (fun s => f s * a) ↔ Function.Surjective f ∧ IsUnit a := by sorry
