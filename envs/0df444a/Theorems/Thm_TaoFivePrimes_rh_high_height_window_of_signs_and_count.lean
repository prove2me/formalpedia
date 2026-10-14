-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_window_of_signs_and_count
-- name    : TaoFivePrimes.rh_high_height_window_of_signs_and_count
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T10:32:00.16467+00:00
-- url     : https://prove2.me/theorems/e4e7aaaf-e445-494b-a3b3-cfa0d63db77d
-- title:
--   TaoFivePrimes.rh_high_height_window_of_signs_and_count
-- statement:
--   The exact closed high-height window follows from actual opposite normalized zeta signs at the endpoints of the published 409 ordered brackets, and a full closed-window distinct-zero upper bound of 409. The intrinsic typed bracket geometry and the accepted generic completeness theorem provide the proof. Actual real signs and the complete count remain explicit hypotheses. Tight reproduction of the proposed dyadic boxes is not required.
-- source:
--   Finite structural sign and order certificates, generated from the native FLINT 3.6.0 Platt FFT/interpolation proposal on [3289999872,3290000000]. Numeric tests are necessary constructor proof fields and use ordinary decide +kernel. No value containment, total zero count or RH conclusion is asserted. Platt method: DOI 10.1090/mcom/3198. The surrounding project preserves attribution to sometik179 (c9908072-d99a-4431-aad8-a72c6352619a) and Gabewhigham. The interpretation uses the Mathlib completed-zeta normalization from the separately accepted normalization theorem.

import Definitions.Def_TaoFivePrimes_RHHighHeightBracketInterface
import Mathlib

theorem TaoFivePrimes.rh_high_height_window_of_signs_and_count
    (hsigns : ∀ p ∈ RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate,
      RHHighHeight.normalized (RHHighHeightBracketInterface.point p.l)*
      RHHighHeight.normalized (RHHighHeightBracketInterface.point p.r)<0)
    (hcount : (RHHighHeight.windowZeros 3289999872 3290000000).ncard ≤ 409) :
    ∀ s ∈ RHHighHeight.windowZeros 3289999872 3290000000, s.re=1/2 := by sorry
