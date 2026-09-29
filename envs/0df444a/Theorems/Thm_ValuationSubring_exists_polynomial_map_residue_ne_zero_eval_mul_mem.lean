-- Prove2me | Theorems.Thm_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem
-- name    : ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/0d532fed-5e7e-5cf1-addb-df1b07dab689
-- title:
--   Denominator clearing over a valuation subring of L
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, with residue map $\mathrm{IsLocalRing.residue}\ A$ onto its residue field. Let $F$ be a field equipped with an $L$-algebra structure, let $f \in F$ be such that $F$ is finite-dimensional over the intermediate field $L(f) = \mathrm{IntermediateField.adjoin}\ L\ \{f\}$, and let $z \in F$ be arbitrary. Then there is a polynomial $q \in A[X]$ such that, first, the image of $q$ under coefficientwise reduction along the residue map of $A$ is a nonzero polynomial over the residue field of $A$, and second, for every valuation subring $V$ of $F$ which contains the image $\mathrm{algebraMap}\ L\ F\ (a)$ of every $a \in L$ and contains $f$, the product $q(f) \cdot z$ lies in $V$, where $q(f)$ denotes $\mathrm{Polynomial.eval}_2$ of $q$ at $f$ along the ring homomorphism $A \hookrightarrow L \to F$ obtained by composing the inclusion of $A$ in $L$ with the structure map of $F$. No hypothesis is placed on $z$ beyond membership in $F$.
--
--   This is the Gauss-style clearing of denominators over a valuation subring: the denominator $q(f)$ which makes $z$ lie in every valuation subring of $F$ containing $L$ and $f$ (equivalently, makes $q(f)z$ integral over $L[f]$) can be taken with coefficients in $A$ and with nonzero reduction modulo the maximal ideal of $A$. It is used in the full-rank part of [`AlgebraicCurve.RegularProlongation.forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed`](thm.html#AlgebraicCurve.RegularProlongation.forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed), where the nonvanishing of the reduction $\bar q$ is what makes the reduced denominator usable at the residue level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z : F) :
    ∃ q : Polynomial A, (q.map (IsLocalRing.residue A)) ≠ 0 ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V →
        (Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q) * z ∈ V := by sorry
