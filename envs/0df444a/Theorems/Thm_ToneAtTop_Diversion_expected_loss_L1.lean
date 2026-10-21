-- Prove2me | Theorems.Thm_ToneAtTop_Diversion_expected_loss_L1
-- name    : ToneAtTop.Diversion.expected_loss_L1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:01.514892+00:00
-- url     : https://prove2.me/theorems/a6ea8891-bc71-4c7e-b7ca-ca968d4758ca
-- title:
--   Appendix, p. 28 — the $L_1(c)$ closed form
-- statement:
--   Under the diversion model's standing assumptions, let $0\le c<1-\tau/\bar x$. The high type can still divert for sufficiently large temptations. The authority's expected loss, computed from both CEO types' choices, equals
--
--   $$
--   L(c)=\frac{2\lambda\bar x+(1-c)^2\bar x^2-p\tau^2}{2(1-c)\bar x}.
--   $$
--
--   This identifies the first loss region used in Lemma 1 and Proposition 1. The statement computes $L$ from its integral definition rather than taking this closed form as a definition.
-- source:
--   Penno, A Theory of Assurance: Balancing Costly Formal Control with Tone at the Top, SSRN working paper 2876700 (revision of May 2019), p. 28 (PDF 30), Appendix, proof of Lemma 1, paragraph beginning “Next note that L1(c) simplifies”

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model

namespace ToneAtTop.Diversion

/-- Closed form of the loss in the high type's diversion region, Appendix p. 28. -/
theorem expected_loss_L1 (P : Params) (hS : P.Standing) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1 - P.tau / P.xbar) :
    expectedLoss P c =
      (2 * P.lam * P.xbar + (1 - c) ^ 2 * P.xbar ^ 2 - P.p * P.tau ^ 2) /
        (2 * (1 - c) * P.xbar) := by sorry

end ToneAtTop.Diversion
