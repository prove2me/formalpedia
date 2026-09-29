-- Prove2me | Theorems.Thm_ValuationSubring_exists_aeval_div_eq_aeval_div_add_aeval_inv_div
-- name    : ValuationSubring.exists_aeval_div_eq_aeval_div_add_aeval_inv_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/d4d02fb6-3375-5380-a84d-2c6ede96a9be
-- title:
--   Laurent decomposition of rational functions over a valuation ring
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring, and let $F$ be a field extension of $L$ containing an element $f$ transcendental over $L$. Let $p, t \in L[X]$ be polynomials such that every coefficient of $p$ lies in $A$, and such that for some index $d$ the valuation attached to $A$ takes the value $1$ on the coefficient $t_d$ while taking value $< 1$ on every coefficient $t_j$ with $j \neq d$ (so $t_d$ is a unit of $A$ and all other coefficients lie in the maximal ideal). Then there exist polynomials $p_1, t_1, q, s \in L[X]$ such that all coefficients of $p_1$ and all coefficients of $q$ lie in $A$; the constant coefficients of $t_1$ and of $s$ each have valuation $1$, while all their remaining coefficients have valuation $< 1$; and, evaluating polynomials at $f$ and at $f^{-1}$ inside $F$,
--   $$\frac{p(f)}{t(f)} = \frac{p_1(f)}{t_1(f)} + \frac{q(f^{-1})}{s(f^{-1})}.$$
--   In particular the denominators on the right are normalised so that the distinguished unit coefficient sits in degree $0$.
--
--   This is the algebraic form of the vanishing of the first Čech cohomology of the structure sheaf on the projective $f$-line over $A$, localised along its special fibre: a section over the overlap of the two standard charts splits as a sum of a section over each chart. It feeds the refined decomposition [`ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv`](thm.html#ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv), where the part at infinity is further separated into a polynomial tail in $f^{-1}$ and a remainder.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_aeval_div_eq_aeval_div_add_aeval_inv_div.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem ValuationSubring.exists_aeval_div_eq_aeval_div_add_aeval_inv_div
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    (p t : L[X]) (hp : ∀ j, p.coeff j ∈ A)
    (ht : ∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1) :
    ∃ p₁ t₁ q s : L[X],
      (∀ j, p₁.coeff j ∈ A) ∧ (∀ j, q.coeff j ∈ A) ∧
      (A.valuation (t₁.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t₁.coeff j) < 1) ∧
      (A.valuation (s.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (s.coeff j) < 1) ∧
      aeval f p / aeval f t = aeval f p₁ / aeval f t₁ + aeval f⁻¹ q / aeval f⁻¹ s := by sorry
