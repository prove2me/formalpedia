-- Prove2me | Theorems.Thm_QEC_Locality_bkScaleRecurrence_mono
-- name    : QEC.Locality.bkScaleRecurrence_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:13:49.030209+00:00
-- url     : https://prove2.me/theorems/b3bfbdde-7270-4f8d-a9d4-9a9cb2048ce5
-- title:
--   Locality: bk Scale Recurrence mono
-- statement:
--   The worst-case finite BK scale recurrence is monotone in its scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L202-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L202-L231

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkScaleRecurrence_mono
    (G : ConnectivityGraph ι) (d : Nat) {small large : Nat} (hscale : small ≤ large) :
    bkScaleRecurrence G d small ≤ bkScaleRecurrence G d large := by sorry
