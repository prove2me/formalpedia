-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_signs_of_tolerance
-- name    : TaoFivePrimes.rh_high_height_signs_of_tolerance
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T12:22:59.531704+00:00
-- url     : https://prove2.me/theorems/4fd6dea9-cd96-41aa-9a26-9dd82776a62c
-- title:
--   TaoFivePrimes.rh_high_height_signs_of_tolerance
-- statement:
--   Each of the 409 proposed bracket endpoint midpoint values has a proved margin larger than 2^-20. Thus any evaluation of the normalized zeta function within 2^-20 of those midpoint values proves the required opposite signs. The concrete finite margins are kernel checked. The actual evaluation error remains an explicit unproved hypothesis, and no RH count or window is asserted.
-- source:
--   Ordinary Lean arithmetic on the previously published typed 409-bracket certificate. Balanced margin proofs avoid reducing a giant array. External proposal generated with FLINT 3.6.0 and the Platt FFT/interpolation method (DOI 10.1090/mcom/3198). Surrounding xi/theta work credits sometik179 (c9908072-d99a-4431-aad8-a72c6352619a) and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighHeightBracketInterface

theorem TaoFivePrimes.rh_high_height_signs_of_tolerance :
  (∀ p ∈ RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate,
    |RHHighHeight.normalized (RHHighHeightBracketInterface.point p.l)-
      ((p.llo:ℝ)+p.lhi)/(2*RHHighHeightBracketInterface.scale)|≤1/2^20 ∧
    |RHHighHeight.normalized (RHHighHeightBracketInterface.point p.r)-
      ((p.rlo:ℝ)+p.rhi)/(2*RHHighHeightBracketInterface.scale)|≤1/2^20) →
  (∀ p ∈ RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate,
    RHHighHeight.normalized (RHHighHeightBracketInterface.point p.l)*
      RHHighHeight.normalized (RHHighHeightBracketInterface.point p.r)<0) := by sorry
