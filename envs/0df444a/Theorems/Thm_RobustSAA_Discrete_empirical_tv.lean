-- Prove2me | Theorems.Thm_RobustSAA_Discrete_empirical_tv
-- name    : RobustSAA.Discrete.empirical_tv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:02.781825+00:00
-- url     : https://prove2.me/theorems/a5f34d95-025e-47ca-9de1-e37180d315a9
-- title:
--   §10.6, p. 38 — empirical frequencies converge in total variation almost surely
-- statement:
--   Draw an infinite independent sequence with law $F$ on a known finite support. Let $\widehat p_N$ be the frequency vector of its first $N$ observations and $p_F$ the true probability vector. Then
--
--   $$
--   d_{\mathrm{TV}}(\widehat p_N,p_F)\longrightarrow 0\qquad\text{almost surely}.
--   $$
--
--   The paper cites this strong-law consequence as the almost-sure event on which it proves Theorem 4.
--
--   **Formalization Note** The observations are coordinates of the canonical countable product measure; the first coordinate corresponds to the paper's first observation.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §10.6, p. 38, sentence after first display (citing Theorem 11.4.1 of [18])

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Setting

namespace RobustSAA.Discrete

open Filter MeasureTheory

theorem empirical_tv (n : ℕ) (F : ProbabilityMeasure (Fin n)) :
    ∀ᵐ ω ∂dataLaw F,
      Tendsto (fun N => dTV (phat (sample ω N)) (pvec F)) atTop (nhds 0) := by sorry

end RobustSAA.Discrete
