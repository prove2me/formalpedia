-- Prove2me | Theorems.Thm_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le
-- name    : Real.exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/08d98192-b477-514f-9e4a-d4fd7a1fa2c8
-- title:
--   Derivative bounds for the germ slog s of a positive definite binary form
-- statement:
--   Let $\alpha,\beta$ be real numbers with $\alpha>0$ and $\beta>0$, and let $f\colon\mathbb R\times\mathbb R\to\mathbb R$ be the function $f(x,y)=s\log s$ with $s=\alpha x^{2}+\beta y^{2}$, the logarithm being Mathlib's `Real.log` (so that the value at the origin is $0$). The assertion is that there exists a real constant $C$ with $0\le C$ such that two things hold simultaneously: first, $f$ is $C^{\infty}$ on the set $\{p\in\mathbb R\times\mathbb R \mid p\neq 0\}$, in the sense of `ContDiffOn` with smoothness index $\top$ in $\mathbb N^{\infty}$; second, for every natural number $n\le 4$ and every $p\neq 0$,
--   $$\|p\|^{n}\,\bigl\|\,\mathrm{iteratedFDeriv}_{\mathbb R}^{\,n} f\,(p)\bigr\| \le C\,\|p\|^{2}\,\bigl(1+|\log\|p\||\bigr),$$
--   where the $n$-th iterated Fréchet derivative at $p$ is measured in the operator norm on continuous $n$-multilinear maps, and $\|p\|$ is the norm of the product $\mathbb R\times\mathbb R$, namely $\max(|x|,|y|)$. The constant $C$ is uniform in $n\le 4$ and in $p$, but depends on $\alpha$ and $\beta$; no bound is claimed for $n\ge 5$.
--
--   This is the quantitative statement that the germ $s\log s$ of a positive definite binary quadratic form behaves, through four derivatives, like a homogeneous function of degree two up to a single logarithmic factor. It is the input for the Fourier-decay estimate [`MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le`](thm.html#MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le), which treats the singular part of the germ attached to a complex place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Real.exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ => (α * p.1 ^ 2 + β * p.2 ^ 2) * Real.log (α * p.1 ^ 2 + β * p.2 ^ 2))
        {p : ℝ × ℝ | p ≠ 0} ∧
      ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 →
        ‖p‖ ^ n *
            ‖iteratedFDeriv ℝ n
                (fun p : ℝ × ℝ => (α * p.1 ^ 2 + β * p.2 ^ 2) * Real.log (α * p.1 ^ 2 + β * p.2 ^ 2))
                p‖ ≤
          C * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|) := by sorry
