-- Prove2me | Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_le_bkScaleRecurrence_card
-- name    : QEC.Locality.bkSeparatorRecurrence_le_bkScaleRecurrence_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:06.986976+00:00
-- url     : https://prove2.me/theorems/62486ec0-1f8c-4501-9325-d5d7e943c922
-- title:
--   Locality: bk Separator Recurrence le bk Scale Recurrence card
-- statement:
--   The charge of every concrete chosen separator tree is bounded by `S_d` at its size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L467-L511
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L467-L511

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

theorem QEC.Locality.bkSeparatorRecurrence_le_bkScaleRecurrence_card
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) :
    bkSeparatorRecurrence G d vertices ≤ bkScaleRecurrence G d vertices.card := by sorry
