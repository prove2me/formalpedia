-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_window_endpoint_signs
-- name    : TaoFivePrimes.rh_high_height_window_endpoint_signs
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T10:31:15.430856+00:00
-- url     : https://prove2.me/theorems/1d76315c-1647-4002-954e-8ae68a71bbc5
-- title:
--   TaoFivePrimes.rh_high_height_window_endpoint_signs
-- statement:
--   The actual normalized completed-zeta values have opposite strict signs at every endpoint pair of the 409 published ordered brackets. This is the primary open numerical-evaluation goal. A rigorous finite evaluator may choose enough precision to prove these signs; reproducing the tight 64-bit proposed boxes is optional. Native FLINT signs are proposals, not Lean proofs.
-- source:
--   High-height 128-unit certificate prototype for the existing TaoFivePrimes finite-RH work. Platt FFT/interpolation proposals and native total counts motivate these exact goals; neither is a Lean proof. The normalized-function, bracket-completeness, finiteness, Turing offset and structural data ingredients are proved separately. Platt method: DOI 10.1090/mcom/3198. The original surrounding xi/theta work credits sometik179, c9908072-d99a-4431-aad8-a72c6352619a, and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighHeightBracketInterface

theorem TaoFivePrimes.rh_high_height_window_endpoint_signs : ∀ p ∈ RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate, RHHighHeight.normalized (RHHighHeightBracketInterface.point p.l)*RHHighHeight.normalized (RHHighHeightBracketInterface.point p.r)<0 := by sorry
