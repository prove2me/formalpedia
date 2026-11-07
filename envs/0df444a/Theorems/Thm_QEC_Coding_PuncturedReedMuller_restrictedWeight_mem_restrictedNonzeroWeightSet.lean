-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_restrictedWeight_mem_restrictedNonzeroWeightSet
-- name    : QEC.Coding.PuncturedReedMuller.restrictedWeight_mem_restrictedNonzeroWeightSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:27.332086+00:00
-- url     : https://prove2.me/theorems/6d5098c1-d91d-4c67-8a9f-37ff3b9a301c
-- title:
--   Punctured Reed Muller: restricted Weight mem restricted Nonzero Weight Set
-- statement:
--   Every actual nonzero RM word contributes its restricted weight to the
--   minimum spectrum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L802-L806
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L802-L806

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.restrictedWeight_mem_restrictedNonzeroWeightSet
    {r m w : Nat} {word : Word (ZMod 2) (BooleanPoint m)}
    (hword : word ∈ (reedMullerCode r m).carrier) (hnonzero : word ≠ 0) :
    restrictedWeight w word ∈ restrictedNonzeroWeightSet r m w := by sorry
