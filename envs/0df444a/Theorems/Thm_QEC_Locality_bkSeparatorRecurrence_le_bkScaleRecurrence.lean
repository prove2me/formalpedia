-- Prove2me | Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_le_bkScaleRecurrence
-- name    : QEC.Locality.bkSeparatorRecurrence_le_bkScaleRecurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:13:53.011203+00:00
-- url     : https://prove2.me/theorems/b9a30248-c3bd-4f14-b025-8e147d39f52a
-- title:
--   Locality: bk Separator Recurrence le bk Scale Recurrence
-- statement:
--   Every concrete recursive charge below scale `r` is dominated by `S_d(r)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L514-L519
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L514-L519

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

theorem QEC.Locality.bkSeparatorRecurrence_le_bkScaleRecurrence
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) (r : Nat)
    (hcard : vertices.card ≤ r) :
    bkSeparatorRecurrence G d vertices ≤ bkScaleRecurrence G d r := by sorry
