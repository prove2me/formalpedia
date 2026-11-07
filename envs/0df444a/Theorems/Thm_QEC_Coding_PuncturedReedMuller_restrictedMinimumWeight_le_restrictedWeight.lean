-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_restrictedMinimumWeight_le_restrictedWeight
-- name    : QEC.Coding.PuncturedReedMuller.restrictedMinimumWeight_le_restrictedWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:28.220979+00:00
-- url     : https://prove2.me/theorems/4449dfe5-a702-429b-acbc-26660a71def4
-- title:
--   Punctured Reed Muller: restricted Minimum Weight le restricted Weight
-- statement:
--   The concrete restricted minimum is no larger than the restricted weight of
--   each actual nonzero Reed--Muller evaluation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L810-L814
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L810-L814

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.restrictedMinimumWeight_le_restrictedWeight
    {r m w : Nat} {word : Word (ZMod 2) (BooleanPoint m)}
    (hword : word ∈ (reedMullerCode r m).carrier) (hnonzero : word ≠ 0) :
    restrictedMinimumWeight r m w ≤ restrictedWeight w word := by sorry
