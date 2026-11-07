-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_puncturedReedMullerCode_relativeMinimumDistance_shortened
-- name    : QEC.Coding.PuncturedReedMuller.puncturedReedMullerCode_relativeMinimumDistance_shortened
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:04:36.448476+00:00
-- url     : https://prove2.me/theorems/fe4045ea-10c9-4908-8370-ea4bd30c5a0f
-- title:
--   Punctured Reed Muller: punctured Reed Muller Code relative Minimum Distance shortened
-- statement:
--   The attained logical coset distance of puncturing modulo shortening is the
--   same HH18 binomial tail.  The witness is the concrete vanishing-polynomial
--   word whose low block is nonzero, not merely an arbitrary nonzero punctured
--   word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L2009-L2051
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L2009-L2051

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.puncturedReedMullerCode_relativeMinimumDistance_shortened
    {m r w : Nat} (hnoKernel : w < m - r) :
    RelativeMinimumDistance (puncturedReedMullerCode r m w)
      (shortenedReedMullerCode r m w) (binomialTail (m - r) w) := by sorry
