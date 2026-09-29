-- Prove2me | Theorems.Thm_ProbabilityTheory_integrable_of_integrable_sq
-- name    : ProbabilityTheory.integrable_of_integrable_sq
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T01:22:11.968019+00:00
-- url     : https://prove2.me/theorems/981c7723-85ab-4167-8140-0860de7c1ecb
-- title:
--   Square-integrable implies integrable on a probability space
-- statement:
--   **$L^2 \subseteq L^1$ on a probability space.** If $Z$ is measurable and $Z^2$ is integrable with respect to a probability measure, then $Z$ is integrable.
--
--   This is the simplest instance of the inclusion $L^q \subseteq L^p$ for $p \le q$ on a finite measure space. The finiteness of the measure is essential: on the line with Lebesgue measure, $Z(x) = 1/(1+|x|)$ is square integrable but not integrable.
--
--   **Proof.** From $(|z| - 1)^2 \ge 0$ one gets the pointwise bound $|z| \le (1 + z^2)/2$. The right-hand side, as a function of $\omega$, is integrable — the constant is integrable because the measure is finite, and $Z^2$ is integrable by hypothesis — so `Integrable.mono` applies.
-- source:
--   W. Rudin, Real and Complex Analysis, 3rd ed., McGraw-Hill 1987, Chapter 3; P. Billingsley, Probability and Measure, 3rd ed., Wiley 1995, Section 21.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem ProbabilityTheory.integrable_of_integrable_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Measurable Z)
    (hsq : Integrable (fun ω => (Z ω) ^ 2) μ) :
    Integrable Z μ := by sorry
