-- Prove2me | Theorems.Thm_ValuationSubring_exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem
-- name    : ValuationSubring.exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/da97aea7-fca8-52fb-bdd8-15ec36c6ac08
-- title:
--   Regularity on both f-charts forces constancy
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $F$ a field equipped with an $L$-algebra structure; let $f \in F$ be transcendental over $L$. Let $t, t' \in L[X]$ be polynomials whose coefficients satisfy, with respect to the valuation attached to $A$: the constant coefficient has valuation exactly $1$ (so it is a unit of $A$), and every coefficient of positive degree has valuation strictly less than $1$ (so it lies in the maximal ideal of $A$); the same two conditions are imposed on $t'$. Let $x \in F$ be such that (i) for every valuation subring $V$ of $F$ which contains $\mathrm{algebraMap}\,L\,F\,(c)$ for all $c \in L$ and contains $f$, the product $x \cdot t(f)$ lies in $V$, and (ii) for every valuation subring $V$ of $F$ containing the image of $L$ and containing $f^{-1}$, the product $x \cdot t'(f^{-1})$ lies in $V$ (the evaluations being taken through the $L$-algebra structure of $F$). Then $x$ is a constant: there exists $c \in L$ with $x = \mathrm{algebraMap}\,L\,F\,(c)$.
--
--   This is the algebraic form of the statement that a function regular on both charts of the normalised $f$-model of $F$ over the valuation ring $A$, after Zariski localisation along the special fibre, is constant, the two polynomials $t(f)$ and $t'(f^{-1})$ being the admissible denominators on the two charts. It is used in the construction of regular prolongations for algebraic curves, in the lemmas identifying residues with images of constants under the structure map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem ValuationSubring.exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    (t t' : L[X])
    (ht : A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1)
    (ht' : A.valuation (t'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t'.coeff j) < 1)
    (x : F)
    (hx : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → x * aeval f t ∈ V)
    (hx' : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
      x * aeval f⁻¹ t' ∈ V) :
    ∃ c : L, x = algebraMap L F c := by sorry
