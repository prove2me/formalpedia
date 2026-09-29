-- Prove2me | Theorems.Thm_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul
-- name    : ValuationSubring.exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/fbf7e0ee-f590-57b9-9664-c1664ea4d10c
-- title:
--   Zariski-local integrality of Gauss-ring coordinates of an integral element
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring, $F$ a field that is an $L$-algebra, and $f\in F$ transcendental over $L$; let $\iota$ be a finite index type and $z:\iota\to F$ a family such that (i) each $z_i$ lies in every valuation subring $V$ of $F$ that contains the image of $L$ and contains $f$, and (ii) $z$ is linearly independent over the intermediate field $L(f)=L(\{f\})$. Call $w\in F$ *Gauss-integral* if $w\,q(f)=p(f)$ for some $p,q\in L[X]$ with all coefficients of $p$ in $A$, all coefficients of $q$ of valuation $\le 1$ and at least one coefficient of $q$ of valuation exactly $1$; call it *Gauss-small* if the same holds with all coefficients of $p$ of valuation $<1$. Assume the residual generation hypothesis: whenever $y\in F$ lies in all the valuation subrings of $F$ as in (i) and $y=\sum_i w_i z_i$ with every $w_i$ Gauss-integral, there are polynomials $C_i\in L[X]$ with all coefficients in $A$ and Gauss-small elements $\mu_i$ with $y=\sum_i (C_i(f)+\mu_i)z_i$. Then for $s\in F$ lying in all those valuation subrings, with $s=\sum_i w_i z_i$ and all $w_i$ Gauss-integral, and for each index $i$, there exist $p,t\in L[X]$ with all coefficients of $p$ in $A$, with $t$ of constant coefficient of valuation $1$ and all higher coefficients of valuation $<1$, such that $w_i=p(f)/t(f)$.
--
--   The statement is a Nakayama-type descent for the non-Noetherian ring obtained by localising $A[f]$ along $1+\mathfrak m A[f]$: under the assumption that the $z_i$ generate modulo the maximal ideal times the Gauss span, the coordinates of an element integral over $L[f]$ with respect to an $L(f)$-independent family $z$ have no poles on the special fibre of the chart $f\neq\infty$. It is used in the construction of regular prolongations of curves, through [`AlgebraicCurve.RegularProlongation.exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq`](thm.html#AlgebraicCurve.RegularProlongation.exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem ValuationSubring.exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    {ι : Type*} [Fintype ι] (z : ι → F)
    (hzT : ∀ i, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z i ∈ V)
    (hzind : LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z)
    (hres : ∀ (y : F) (w : ι → F),
      (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y ∈ V) →
      (∀ i, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
        ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
        w i * aeval f q = aeval f p) →
      y = ∑ i, w i * z i →
      ∃ (C₁ : ι → L[X]) (μ : ι → F), (∀ i j, (C₁ i).coeff j ∈ A) ∧
        (∀ i, ∃ p q : L[X], (∀ j, A.valuation (p.coeff j) < 1) ∧
          ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
          μ i * aeval f q = aeval f p) ∧
        y = ∑ i, (aeval f (C₁ i) + μ i) * z i)
    (s : F) (w : ι → F)
    (hsT : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → s ∈ V)
    (hw : ∀ i, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
      ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
      w i * aeval f q = aeval f p)
    (hs : s = ∑ i, w i * z i) (i : ι) :
    ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
      (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
      w i = aeval f p / aeval f t := by sorry
