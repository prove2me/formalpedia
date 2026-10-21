-- Prove2me | Theorems.Thm_PrefRobustSR_WorstCase_jensen_step
-- name    : PrefRobustSR.WorstCase.jensen_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:36.16399+00:00
-- url     : https://prove2.me/theorems/b403b9bf-2abe-4663-bbf8-cdcafac9123c
-- title:
--   Proof of Theorem 2.1, p. 7: Jensen's inequality
-- statement:
--   Let $P$ be a probability measure, let $l\in\mathcal L$, let $Z$ be an integrable real position, and let $t\in\mathbb R$. Jensen's inequality gives
--   $$
--   \mathbb E_P[l(-Z-t)]\ge l(-\mathbb E_P[Z]-t).
--   $$
--   The inequality remains meaningful when the expected loss is $+\infty$, which is needed for unbounded losses.
--
--   **Formalization Note** This proof step assumes `Integrable Z P`, which follows from the paper's $Z\in\mathcal L_p$ on a probability space for $1\le p<\infty$. The loss expectation is extended; $\mathbb E_P[Z]$ is the ordinary integral because $Z$ is integrable.
-- source:
--   Delage, Guo & Xu, Shortfall risk models when information of loss function is incomplete, preprint dated April 25, 2018 (later article DOI: https://doi.org/10.1287/opre.2021.2212; numbering follows the preprint), p. 7, proof of Theorem 2.1, Jensen inequality preceding (2.11)

import Mathlib
import Definitions.Def_PrefRobustSR_WorstCase_Model

namespace PrefRobustSR.WorstCase

open MeasureTheory

/-- Jensen's inequality as used in the proof of Theorem 2.1, p. 7. -/
theorem jensen_step {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (l : ℝ → ℝ) (hl : l ∈ LossClass) (Z : Ω → ℝ)
    (hZ : Integrable Z P) (t : ℝ) :
    ((l (-(∫ ω, Z ω ∂P) - t) : ℝ) : EReal) ≤
      DupacovaWets.Consistency.expect P
        (fun ω => ((l (-Z ω - t) : ℝ) : EReal)) := by sorry

end PrefRobustSR.WorstCase
