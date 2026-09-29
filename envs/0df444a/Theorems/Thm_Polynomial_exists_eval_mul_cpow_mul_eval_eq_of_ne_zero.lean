-- Prove2me | Theorems.Thm_Polynomial_exists_eval_mul_cpow_mul_eval_eq_of_ne_zero
-- name    : Polynomial.exists_eval_mul_cpow_mul_eval_eq_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/e2da9541-6651-510e-9db3-043646b1a4ff
-- title:
--   Clearing denominators for a ratio of q^s-rational functions
-- statement:
--   Let $q$ be a non-zero complex number, let $P,P^\vee,Q,Q^\vee\in\mathbb{C}[X]$ with $P\neq 0$ and $Q^\vee\neq 0$, and let $m,m^\vee\in\mathbb{Z}$; no hypothesis is imposed on $P^\vee$ or $Q$. The assertion is that there exist polynomials $R_1,R_2\in\mathbb{C}[X]$ and an integer $r$ with $R_2\neq 0$ such that, for every $s\in\mathbb{C}$,
--   $$R_2(q^{s})\cdot\bigl(q^{m^\vee s}P^\vee(q^{-s})\bigr)\cdot Q(q^{s})\;=\;\bigl(R_1(q^{s})\,q^{rs}\bigr)\cdot\bigl(q^{m\cdot(-s)}P(q^{s})\bigr)\cdot Q^\vee(q^{-s}),$$
--   where all powers $q^{z}$ are the principal complex power and the integers $m,m^\vee,r$ are cast into $\mathbb{C}$ in the exponents. Thus the identity is an identity of entire functions of $s$, valid for all complex $s$ rather than on a half-plane, and it is an existence statement: the witnesses $R_1,R_2,r$ are not specified in the conclusion. Concretely the proof produces $R_1=Q\cdot\operatorname{rev}(P^\vee)$, $R_2=P\cdot\operatorname{rev}(Q^\vee)$ and $r=m^\vee+m+\deg Q^\vee-\deg P^\vee$, with $\operatorname{rev}$ the reversal of a polynomial and $\deg$ the `natDegree`.
--
--   This is the elementary bookkeeping step behind the rationality of a local gamma factor: if a local integral and its dual are given, on suitable half-planes, by expressions $q^{ms}P(q^{\pm s})/Q(q^{\pm s})$, then the quotient of the dual at $s$ by the primal at $-s$ again has the normal form $q^{rs}R_1(q^{s})/R_2(q^{s})$, here stated in cleared-denominator form. It is used in the Rankin–Selberg part of the Langlands–Tunnell input, by [`LanglandsTunnell.RankinSelberg.exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_eval_mul_cpow_mul_eval_eq_of_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Polynomial.exists_eval_mul_cpow_mul_eval_eq_of_ne_zero
    (q : ℂ) (hq : q ≠ 0) (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (hP : P ≠ 0) (hQd : Qd ≠ 0) :
    ∃ (R₁ R₂ : Polynomial ℂ) (r : ℤ), R₂ ≠ 0 ∧
      ∀ s : ℂ,
        R₂.eval (q ^ s) * (q ^ ((md : ℂ) * s) * Pd.eval (q ^ (-s))) * Q.eval (q ^ s) =
          (R₁.eval (q ^ s) * q ^ ((r : ℂ) * s)) * (q ^ ((m : ℂ) * (-s)) * P.eval (q ^ s)) * Qd.eval (q ^ (-s)) := by sorry
