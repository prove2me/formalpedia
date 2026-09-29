-- Prove2me | Theorems.Thm_TrigInequalities_cot_half_antitone_on_unit_interval
-- name    : TrigInequalities.cot_half_antitone_on_unit_interval
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T16:26:29.727872+00:00
-- url     : https://prove2.me/theorems/cc17cbc0-d3a4-4592-bf7f-d482cdd134d7
-- title:
--   Antitonicity of $\cot(\pi s)/2$ on the unit interval
-- statement:
--   **$\tfrac12\cot(\pi s)$ is decreasing on $(0,1)$.**
--
--   For $0 < s_1 \le s_2 < 1$,
--
--   $$\frac{\cos(\pi s_2)}{2\sin(\pi s_2)} \;\le\; \frac{\cos(\pi s_1)}{2\sin(\pi s_1)} .$$
--
--   On the open interval $(0,1)$ we have $\sin(\pi s) > 0$, so the quotient is well defined, and it
--   is $\tfrac12\cot(\pi s)$. Its derivative is $-\tfrac{\pi}{2}\csc^{2}(\pi s) < 0$ throughout, so
--   the function is strictly decreasing, running from $+\infty$ at $s \to 0^{+}$ to $-\infty$ at
--   $s \to 1^{-}$ and vanishing at $s = 1/2$.
--
--   The quantity is exactly the imaginary part of the weight
--   $w(s) = (1 - e^{2\pi i s})^{-1}$, whose real part is the constant $\tfrac12$. Monotonicity of
--   $\Im w$ is what makes the weights in the Kusmin–Landau inequality **telescope** rather than
--   accumulate under Abel summation: because the imaginary parts move in one direction, the sum of
--   $|w(n+1) - w(n)|$ is controlled by the total variation across the range instead of being
--   bounded term by term.
--
--   **Formalization note.** The hypotheses $0 < s_1$ and $s_2 < 1$ keep both sines strictly
--   positive, so neither denominator vanishes.
-- source:
--   Elementary; the monotonicity underlying the Kusmin–Landau inequality, cf. Graham & Kolesnik, *van der Corput's Method of Exponential Sums*, §2.1. Lean proof extracted from `Salt/ExpSum/Kusmin.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace TrigInequalities

theorem cot_half_antitone_on_unit_interval {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h12 : s₁ ≤ s₂)
    (h2 : s₂ < 1) :
    Real.cos (Real.pi * s₂) / (2 * Real.sin (Real.pi * s₂))
      ≤ Real.cos (Real.pi * s₁) / (2 * Real.sin (Real.pi * s₁)) := by sorry

end TrigInequalities
