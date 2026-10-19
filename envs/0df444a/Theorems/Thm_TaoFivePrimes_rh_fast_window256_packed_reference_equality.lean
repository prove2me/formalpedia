-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_packed_reference_equality
-- name    : TaoFivePrimes.rh_fast_window256_packed_reference_equality
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:59:53.860021+00:00
-- url     : https://prove2.me/theorems/92eaf94b-df27-4acc-8b1d-8e6381516168
-- title:
--   TaoFivePrimes.rh_fast_window256_packed_reference_equality
-- statement:
--   All24 packed proposed reference rows decode exactly to all2048 words of each original Fourier data table. This is lossless data equality, without an old Fourier accuracy proof.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable

theorem TaoFivePrimes.rh_fast_window256_packed_reference_equality :
 (List.range 24).map (fun k=>(List.range 2048).map (RHFastWindow256CompactReference.raw k))=
  RHHighGammaFourierTable.packets := by sorry
