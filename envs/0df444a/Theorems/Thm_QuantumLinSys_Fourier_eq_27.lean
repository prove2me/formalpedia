-- Prove2me | Theorems.Thm_QuantumLinSys_Fourier_eq_27
-- name    : QuantumLinSys.Fourier.eq_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:01.330914+00:00
-- url     : https://prove2.me/theorems/dacf0c58-a5e8-4f6d-8c1f-f248a9bf7738
-- title:
--   (27), p. 11 — error bound for the truncated Fourier integral
-- statement:
--   Let $x\ne0$ and let $y_J,z_K\ge0$ be cutoffs. For the complex truncated Gaussian Fourier integral $g_{y_J,z_K}$ of (21),
--   $$
--   \left|g_{y_J,z_K}(x)-\frac1x\right|
--   \le \frac{e^{-(xy_J)^2/2}}{|x|}
--      +\frac{2e^{-z_K^2/2}}{|x|}.
--   $$
--
--   This gives the quantitative truncation error used to choose the cutoffs in Lemma 12.
--
--   **Formalization Note** The displayed argument on p. 11 uses $x\ne0$ to divide by $x$, and its cutoffs are nonnegative. The absolute value is the complex norm.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, p. 11, displays (22)–(27)

import Mathlib
import Definitions.Def_QuantumLinSys_Fourier_Setting

namespace QuantumLinSys.Fourier

/-- The truncation error bound (27), p. 11, for the integral (21). -/
theorem eq_27 (x yJ zK : ℝ) (hx : x ≠ 0) (hy : 0 ≤ yJ) (hz : 0 ≤ zK) :
    ‖gTrunc yJ zK x - ((1 / x : ℝ) : ℂ)‖ ≤
      Real.exp (-(x * yJ) ^ 2 / 2) / |x| +
        2 * Real.exp (-zK ^ 2 / 2) / |x| := by sorry

end QuantumLinSys.Fourier
