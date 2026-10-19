-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_real_grid_sign_checks
-- name    : TaoFivePrimes.rh_batch01_height_real_grid_sign_checks
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T17:49:46.124683+00:00
-- url     : https://prove2.me/theorems/3dd96e09-7929-4b56-8bf9-a3959b0154c8
-- title:
--   TaoFivePrimes.rh_batch01_height_real_grid_sign_checks
-- statement:
--   Exact integer margins and opposite proposed signs at both endpoints of each of the409 typed brackets, with all endpoint indices strictly below4096. Seven bounded64-leaf ordinary kernel checks. The theorem concerns proposed integer FFT data only; analytic enclosures and Fourier reconstruction remain explicit prerequisites for zeta signs. No zeta sign, winding, zero count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01RealGrid
import Definitions.Def_TaoFivePrimes_RHBatch01HeightBracketInterface

theorem TaoFivePrimes.rh_batch01_height_real_grid_sign_checks :
 (RHBatch01HeightBracketInterface.leaves RHBatch01HeightBracketData.certificate).all
  (fun p=>decide (p.l<4096 ∧ p.r<4096 ∧ 2^80≤10^8*(RHBatch01RealGrid.value p.l).natAbs ∧ 2^80≤10^8*(RHBatch01RealGrid.value p.r).natAbs ∧ RHBatch01RealGrid.value p.l*RHBatch01RealGrid.value p.r<0))=true := by sorry
