-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_puncturedReedMullerCode_dimension_eq_sum_choose
-- name    : QEC.Coding.PuncturedReedMuller.puncturedReedMullerCode_dimension_eq_sum_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:56.484744+00:00
-- url     : https://prove2.me/theorems/8215591d-725e-48f1-ba92-a738b7015c48
-- title:
--   Punctured Reed Muller: punctured Reed Muller Code dimension eq sum choose
-- statement:
--   Raw source form of punctured Reed--Muller dimension preservation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L1948-L1953
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L1948-L1953

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.puncturedReedMullerCode_dimension_eq_sum_choose
    {m r w : Nat} (hnoKernel : w < m - r) :
    Dimension (puncturedReedMullerCode r m w) =
      ∑ i ∈ Finset.Icc 0 r, Nat.choose m i := by sorry
