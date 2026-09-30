-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_linear_map_unit_multiplier_iff
-- name    : WeierstrassEllipticZeta.linear_map_unit_multiplier_iff
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-11T21:13:20.060966+00:00
-- url     : https://prove2.me/theorems/1b763d04-4a2e-47e4-a051-660e7d5b1d48
-- title:
--   Bijective multiplication operators and unique unit multipliers
-- statement:
--   Let $R$ be a commutative semiring and let $A$ be a semiring equipped with an $R$-algebra structure. For $b\in A$, write $L_b(a)=ba$ for the $R$-linear operator of left multiplication. Let $A^\times$ be the group of units of $A$.
--
--   Every $R$-linear endomorphism $T:A\to A$ satisfies
--   $$
--   \bigl((\exists! b\in A,\ T=L_b)\ \land\ T\text{ is bijective}\bigr)
--   \quad\Longleftrightarrow\quad
--   \exists! u\in A^\times,\ T=L_u.
--   $$
--
--   This characterizes which multiplication operators are linear automorphisms and gives a unique unit parameter for each. The target semiring may be noncommutative or trivial; no field or finite-dimensionality assumption is required.
-- source:
--   Derived supporting algebra lemma for the Senthil Kumar mission: for an R-linear endomorphism T of an R-algebra A, being multiplication by a unique element and being bijective is equivalent to being multiplication by a unique unit. R is a commutative semiring; A is an arbitrary semiring. At Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, Algebra.lmul_injective and Algebra.lmul_isUnit_iff are in Algebra/Algebra/Bilinear.lean lines 154-160; Module.End.isUnit_iff is in Algebra/Module/Equiv/Basic.lean lines 65-69. Primary documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Bilinear.html and https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Equiv/Basic.html . This is an inferred supporting lemma, not a separately quoted theorem of the article. It requires no commutativity of A, field, finite-dimensionality or nontriviality. No platform theorem dependencies or new definitions.

import Mathlib.Algebra.Algebra.Bilinear

theorem WeierstrassEllipticZeta.linear_map_unit_multiplier_iff
    (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (T : A →ₗ[R] A) :
    ((∃! b : A, T = Algebra.lmul R A b) ∧ Function.Bijective T) ↔
      ∃! u : Aˣ, T = Algebra.lmul R A (u : A) := by sorry
