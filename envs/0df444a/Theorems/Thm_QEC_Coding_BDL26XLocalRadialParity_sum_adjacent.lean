-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_sum_adjacent
-- name    : QEC.Coding.BDL26XLocalRadialParity.sum_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:31:02.41181+00:00
-- url     : https://prove2.me/theorems/3c45ccac-2ece-4324-bbd8-b4db1b5733b9
-- title:
--   BDL26 XLocal Radial Parity: sum adjacent
-- statement:
--   Binary cancellation along every adjacent pair of a finite interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L21-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L21-L38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.sum_adjacent (n : ℕ) (f : Fin (n + 1) → Field) :
    (∑ i : Fin n, (f i.castSucc + f i.succ)) = f 0 + f (Fin.last n) := by sorry
