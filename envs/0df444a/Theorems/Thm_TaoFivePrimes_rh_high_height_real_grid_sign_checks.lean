-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_real_grid_sign_checks
-- name    : TaoFivePrimes.rh_high_height_real_grid_sign_checks
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:48:52.294779+00:00
-- url     : https://prove2.me/theorems/3796358f-76b7-4c05-9719-9ea64be02660
-- title:
--   TaoFivePrimes.rh_high_height_real_grid_sign_checks
-- statement:
--   Exact integer margins and opposite proposed signs at both endpoints of each of the409 typed brackets, with all endpoint indices strictly below4096. Seven bounded64-leaf ordinary kernel checks. The theorem concerns proposed integer FFT data only; analytic enclosures and Fourier reconstruction remain explicit prerequisites for zeta signs. No zeta sign, winding, zero count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighRealGrid
import Definitions.Def_TaoFivePrimes_RHHighHeightBracketInterface

theorem TaoFivePrimes.rh_high_height_real_grid_sign_checks :
 (RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate).all
  (fun p=>decide (p.l<4096 ∧ p.r<4096 ∧ 2^80≤10^8*(RHHighRealGrid.value p.l).natAbs ∧ 2^80≤10^8*(RHHighRealGrid.value p.r).natAbs ∧ RHHighRealGrid.value p.l*RHHighRealGrid.value p.r<0))=true := by sorry
