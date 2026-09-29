-- Prove2me | Theorems.Thm_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv
-- name    : ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/33e23593-e6b3-5574-b9fa-e8501db8c3f1
-- title:
--   Decomposition of p(f)/t(f) with f^{-m}-tail and polynomial part
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring, with $A.\mathrm{valuation}$ its associated valuation; let $F$ be a field which is an $L$-algebra and $f \in F$ an element transcendental over $L$. Let $p, t \in L[X]$ be such that every coefficient of $p$ lies in $A$, and such that for some index $d$ the coefficient $t_d$ has valuation exactly $1$ while all other coefficients of $t$ have valuation $< 1$. Then for every natural number $m$ there exist polynomials $p_1, t_1, q, s, r \in L[X]$ such that all coefficients of $p_1$, of $q$ and of $r$ lie in $A$, the degree of $r$ is less than $m$, both $t_1$ and $s$ have constant coefficient of valuation $1$ and all higher coefficients of valuation $< 1$, and the identity
--   $$\frac{p(f)}{t(f)} = \frac{p_1(f)}{t_1(f)} + (f^{-1})^m \cdot \frac{q(f^{-1})}{s(f^{-1})} + r(f^{-1})$$
--   holds in $F$, where evaluation is the $L$-algebra map $\mathrm{aeval}$ at $f$, respectively at $f^{-1}$.
--
--   In the language of the projective $f$-line over the valuation ring $A$, localised along its special fibre, the assertion is that the ring $\Lambda$ of elements $p(f)/t(f)$ with the stated coefficient conditions equals $\Lambda_+ + f^{-m}\Lambda_- + \sum_{0 \le i < m} A f^{-i}$, the refinement by a polynomial tail in $f^{-1}$ of the plain two-piece (Čech) decomposition. It is used in the construction of regular prolongations for algebraic curves, in the computation that matches a sum of local contributions against a total dimension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    (p t : L[X]) (hp : ∀ j, p.coeff j ∈ A)
    (ht : ∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1)
    (m : ℕ) :
    ∃ p₁ t₁ q s r : L[X],
      (∀ j, p₁.coeff j ∈ A) ∧ (∀ j, q.coeff j ∈ A) ∧ (∀ j, r.coeff j ∈ A) ∧ r.degree < m ∧
      (A.valuation (t₁.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t₁.coeff j) < 1) ∧
      (A.valuation (s.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (s.coeff j) < 1) ∧
      aeval f p / aeval f t =
        aeval f p₁ / aeval f t₁ + (f⁻¹) ^ m * (aeval f⁻¹ q / aeval f⁻¹ s) + aeval f⁻¹ r := by sorry
