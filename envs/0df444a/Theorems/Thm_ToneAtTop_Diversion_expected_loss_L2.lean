-- Prove2me | Theorems.Thm_ToneAtTop_Diversion_expected_loss_L2
-- name    : ToneAtTop.Diversion.expected_loss_L2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:01.208288+00:00
-- url     : https://prove2.me/theorems/424d9e55-3d33-460e-944b-4825c3979514
-- title:
--   Equation (A1), p. 28 — the $L_2(c)$ closed form
-- statement:
--   Under the diversion model's standing assumptions, let $1-\tau/\bar x\le c<1$. The high CEO type does not divert for any temptation in $[0,\bar x]$. The authority's expected loss is
--
--   $$
--   L(c)=\frac12(1-p)(1-c)\bar x+\frac{\lambda}{1-c}.
--   $$
--
--   This is equation (A1), the loss in the second region. It follows from the utility-based integral definition of $L$.
-- source:
--   Penno, A Theory of Assurance: Balancing Costly Formal Control with Tone at the Top, SSRN working paper 2876700 (revision of May 2019), p. 28 (PDF 30), Appendix, proof of Lemma 1, eq. (A1)

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model

namespace ToneAtTop.Diversion

/-- The no-high-type-diversion loss, (A1). -/
theorem expected_loss_L2 (P : Params) (hS : P.Standing) (c : ℝ)
    (hc0 : 1 - P.tau / P.xbar ≤ c) (hc1 : c < 1) :
    expectedLoss P c =
      (1 / 2 : ℝ) * (1 - P.p) * (1 - c) * P.xbar + P.lam / (1 - c) := by sorry

end ToneAtTop.Diversion
