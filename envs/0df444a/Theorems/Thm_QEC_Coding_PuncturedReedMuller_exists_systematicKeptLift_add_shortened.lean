-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_exists_systematicKeptLift_add_shortened
-- name    : QEC.Coding.PuncturedReedMuller.exists_systematicKeptLift_add_shortened
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:25.726739+00:00
-- url     : https://prove2.me/theorems/824c9274-be68-4229-8b0c-97dec80bdfd2
-- title:
--   Punctured Reed Muller: exists systematic Kept Lift add shortened
-- statement:
--   Every punctured word splits into a systematic lift plus a shortened word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L351-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L351-L382

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.exists_systematicKeptLift_add_shortened {w r m : Nat}
    (h : Admissible w r m)
    {word : Word (ZMod 2) (KeptPoint m w)}
    (hword : word ∈ (puncturedReedMullerCode r m w).carrier) :
    ∃ logical shortened,
      shortened ∈ (shortenedReedMullerCode r m w).carrier ∧
        systematicKeptLift h logical + shortened = word := by sorry
