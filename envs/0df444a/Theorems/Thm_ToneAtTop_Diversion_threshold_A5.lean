-- Prove2me | Theorems.Thm_ToneAtTop_Diversion_threshold_A5
-- name    : ToneAtTop.Diversion.threshold_A5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:05.786204+00:00
-- url     : https://prove2.me/theorems/0885400a-2148-41e0-a6c8-61cdc895c77d
-- title:
--   Equation (A5), p. 28 — the branch threshold
-- statement:
--   Assume the standing diversion model and $\tau<\sqrt{2\lambda\bar x/p}$. At the first-region first-order candidate, its high-type tipping point is no greater than the maximum temptation exactly when $\tau$ is below the branch threshold:
--
--   $$
--   \frac{\tau\bar x}{\sqrt{2\lambda\bar x-p\tau^2}}\le\bar x
--   \quad\Longleftrightarrow\quad
--   \tau\le\sqrt{\frac{2\lambda\bar x}{1+p}}.
--   $$
--
--   This is the comparison behind equation (A5), separating the two cases of Proposition 1. Positivity of the square-root argument follows from the displayed Lemma 1 condition and the standing assumptions.
-- source:
--   Penno, A Theory of Assurance: Balancing Costly Formal Control with Tone at the Top, SSRN working paper 2876700 (revision of May 2019), p. 28 (PDF 30), Appendix, proof of Proposition 1, eq. (A5)

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model

namespace ToneAtTop.Diversion

/-- Equation (A5) locates where the interior solution reaches the kink. -/
theorem threshold_A5 (P : Params) (hS : P.Standing)
    (hL1a : P.tau < Real.sqrt (2 * P.lam * P.xbar / P.p)) :
    P.tau * P.xbar /
        Real.sqrt (2 * P.lam * P.xbar - P.p * P.tau ^ 2) ≤ P.xbar ↔
      P.tau ≤ Real.sqrt (2 * P.lam * P.xbar / (1 + P.p)) := by sorry

end ToneAtTop.Diversion
