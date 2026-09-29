-- Prove2me | Theorems.Thm_PerronKernels_integrable_inv_denom
-- name    : PerronKernels.integrable_inv_denom
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:02:34.844498+00:00
-- url     : https://prove2.me/theorems/ffd59c66-cf76-4267-8205-127041cfab8b
-- title:
--   Integrability of the smoothed Perron kernel denominator
-- statement:
--   **The second-order Perron kernel is integrable along a vertical line.**
--
--   For $c > 0$, the function
--
--   $$t \;\longmapsto\; \frac{1}{(c+it)\,(c+it+1)}$$
--
--   is Lebesgue integrable over $t \in \mathbb{R}$.
--
--   The integrand decays like $|t|^{-2}$: both factors have modulus at least $|t|$ for large $|t|$,
--   so the product has modulus $\gtrsim t^{2}$ and the reciprocal is $O(t^{-2})$, which is
--   integrable at infinity. Near $t = 0$ there is no singularity, since $c > 0$ keeps both factors
--   away from zero — this is exactly what the hypothesis buys.
--
--   The quadratic decay is the reason **smoothed** Perron formulas are preferred to the sharp one.
--   The sharp Perron kernel $x^{s}/s$ decays only like $|t|^{-1}$, so its vertical integral
--   converges conditionally at best and must be truncated with an error term. Replacing it by the
--   Riesz-mean kernel $x^{s+1}/(s(s+1))$ gives absolute convergence, and the resulting formula
--   requires no truncation — at the cost of computing a smoothed sum rather than a sharp one.
--
--   **Formalization note.** `Integrable` is with respect to Lebesgue measure on $\mathbb{R}$, and
--   the integrand is $\mathbb{C}$-valued.
-- source:
--   Classical; the smoothed (Riesz-mean) Perron kernel, see Montgomery & Vaughan, *Multiplicative Number Theory I*, §5.1. Lean proof extracted from `Salt/SW/Kernel.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace PerronKernels

open MeasureTheory Complex in
theorem integrable_inv_denom {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))⁻¹) := by sorry

end PerronKernels
