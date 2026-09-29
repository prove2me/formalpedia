-- Prove2me | Theorems.Thm_PerronKernels_norm_ofReal_cpow_vert
-- name    : PerronKernels.norm_ofReal_cpow_vert
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:06:53.549019+00:00
-- url     : https://prove2.me/theorems/f6ddbecd-b1df-4535-ae67-5f676f9b2148
-- title:
--   The modulus of $b^{s}$ on a vertical line
-- statement:
--   **A real base raised to a complex exponent has modulus depending only on the real part.**
--
--   For $b \ge 0$, $c > 0$ and any real $t$,
--
--   $$\bigl|b^{\,c+it}\bigr| \;=\; b^{\,c} .$$
--
--   Writing $b^{s} = e^{s\log b}$ for $b > 0$, the modulus is $e^{\Re(s)\log b} = b^{\Re s}$, since
--   the imaginary part contributes the unimodular factor $e^{it\log b}$. The hypothesis $c > 0$
--   handles the boundary case $b = 0$, where $0^{c+it} = 0 = 0^{c}$.
--
--   The identity is what makes vertical-line integrals in Perron and Mellin formulas estimable: on
--   the contour $\Re s = c$ the factor $x^{s}$ has constant modulus $x^{c}$, so it pulls out of any
--   bound and the remaining integrand — typically a kernel like $1/(s(s+1))$ — governs convergence.
--   The choice of the abscissa $c$ then trades the size of $x^{c}$ against the behaviour of the
--   Dirichlet series being integrated.
--
--   **Formalization note.** `(b : ℂ) ^ z` is `Complex.cpow`, whose branch conventions make the
--   hypotheses $b \ge 0$ and $c > 0$ the right ones for the identity to hold without exception.
-- source:
--   Classical; standard in Mellin/Perron analysis, see Montgomery & Vaughan, *Multiplicative Number Theory I*, §5.1. Lean proof extracted from `Salt/SW/Kernel.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace PerronKernels

open Complex in
theorem norm_ofReal_cpow_vert {b : ℝ} (hb : 0 ≤ b) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖(b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ = b ^ c := by sorry

end PerronKernels
