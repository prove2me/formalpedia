-- Prove2me | Theorems.Thm_ProbabilityTheory_cond_real_apply
-- name    : ProbabilityTheory.cond_real_apply
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:06:47.651233+00:00
-- url     : https://prove2.me/theorems/77be608a-2fc3-49a2-847c-f8c68f566650
-- title:
--   The real-valued conditional measure formula
-- statement:
--   **Conditional probability, in real-valued form.**
--
--   For a measurable set $s$ and any set $t$,
--
--   $$\mathbb{P}[\,t \mid s\,] \;=\; \frac{\mathbb{P}(s \cap t)}{\mathbb{P}(s)} ,$$
--
--   stated with the real-valued measure throughout:
--   $\mu[|s]_{\mathbb{R}}(t) = (\mu_{\mathbb{R}}(s))^{-1}\mu_{\mathbb{R}}(s\cap t)$.
--
--   This is the definition of conditioning, but having it in $\mathbb{R}$ rather than $[0,\infty]$
--   is what makes it usable. Probabilistic and information-theoretic arguments work in $\mathbb{R}$,
--   where subtraction and logarithms are available; the `ENNReal` form would require establishing
--   finiteness before every manipulation.
--
--   The identity holds with no hypothesis that $\mu(s) \ne 0$: when $\mu_{\mathbb{R}}(s) = 0$ the
--   inverse is $0$ by Mathlib's convention and both sides vanish, so the degenerate case needs no
--   separate treatment.
--
--   **Formalization note.** `μ[|s]` is `ProbabilityTheory.cond μ s` and `μ.real t` is
--   `(μ t).toReal`; measurability of $s$ is needed for the restriction defining the conditional
--   measure.
-- source:
--   Adapted from the Polynomial Freiman–Ruzsa (PFR) project (Terence Tao and contributors, Apache-2.0), as vendored in `Salt/Entropy/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace ProbabilityTheory

open MeasureTheory ProbabilityTheory in
theorem cond_real_apply {Ω : Type*} {_ : MeasurableSpace Ω} {s : Set Ω}
    (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[|s].real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by sorry

end ProbabilityTheory
