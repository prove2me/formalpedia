-- Prove2me | Theorems.Thm_ValuationSubring_exists_uniform_pow_mul_mem_of_liesOverPrime
-- name    : ValuationSubring.exists_uniform_pow_mul_mem_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/bd0e3ce1-1618-58e4-9142-2d41fb36388e
-- title:
--   Uniform p-power window for a nonzero algebraic number
-- statement:
--   Let $p$ be a prime natural number and let $x$ be a nonzero element of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ (in the Mathlib model `AlgebraicClosure ℚ`). The assertion is the existence of a single exponent $B \in \mathbb N$, depending only on $p$ and $x$, such that for every valuation subring $A$ of $\overline{\mathbb Q}$ satisfying `A.LiesOverPrime p` — that is, the image of $p$ in $\overline{\mathbb Q}$ belongs to `A.nonunits`, the set of elements of $A$ that are not units of $A$, so that $p$ lies in $A$ and generates a proper ideal, equivalently $p$ lies in the maximal ideal of $A$ — both products $p^B x$ and $p^B x^{-1}$ lie in $A$. The point is the order of quantification: the exponent $B$ is chosen before the valuation subring, so one and the same window $B$ works simultaneously for all valuation subrings of $\overline{\mathbb Q}$ in which $p$ is a nonunit, bounding the valuations of both $x$ and $x^{-1}$ from below by $-B$ times the valuation of $p$.
--
--   This is the elementary statement that a nonzero algebraic number and its inverse differ from elements of $\overline{\mathbb Q}$-valuation rings above $p$ by a bounded power of $p$, uniformly in the valuation ring; the content beyond the per-ring case is the uniformity of the exponent. It is used to produce uniform denominator bounds in the treatment of $q$-expansion coefficients and coverings of the modular curves $X_0(N)$, being cited in [`ModularCurve.MultCovering.exists_linkBudget`](thm.html#ModularCurve.MultCovering.exists_linkBudget), [`ModularCurve.exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem`](thm.html#ModularCurve.exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem) and [`ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion`](thm.html#ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_uniform_pow_mul_mem_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_uniform_pow_mul_mem_of_liesOverPrime {p : ℕ} (hp : p.Prime)
    {x : AlgebraicClosure ℚ} (hx : x ≠ 0) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      (p : AlgebraicClosure ℚ) ^ B * x ∈ A ∧ (p : AlgebraicClosure ℚ) ^ B * x⁻¹ ∈ A := by sorry
