-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_totalParity_wordPushforward
-- name    : QEC.Coding.BDL26RZLocalReplacement.totalParity_wordPushforward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:53:58.212942+00:00
-- url     : https://prove2.me/theorems/b91dee65-bfbf-40d7-8378-9a93c8b5d436
-- title:
--   BDL26 RZLocal Replacement: total Parity word Pushforward
-- statement:
--   Finite pushforward preserves the total binary coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16144-L16153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16144-L16153

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.totalParity_wordPushforward {Source Target : Type}
    [Fintype Source] [Fintype Target] [DecidableEq Source] [DecidableEq Target]
    (map : Source → Target) (word : Word Field Source) :
    totalParity (wordPushforward map word) = totalParity word := by sorry
