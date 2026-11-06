-- Prove2me | Theorems.Thm_QEC_Locality_bkScaleRecurrence_eq_profile_add
-- name    : QEC.Locality.bkScaleRecurrence_eq_profile_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:14:08.159846+00:00
-- url     : https://prove2.me/theorems/fba04a1b-a8d3-467e-8868-36026bfb4a2b
-- title:
--   Locality: bk Scale Recurrence eq profile add
-- statement:
--   The Locality construction uses the bk Scale Recurrence eq profile add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L192-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L192-L199

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

theorem QEC.Locality.bkScaleRecurrence_eq_profile_add
    (G : ConnectivityGraph ι) (d r : Nat) (hterminal : ¬bkScaleTerminal d r) :
    bkScaleRecurrence G d r =
      twoThirdsSeparationProfile G r +
        bkScaleRecurrence G d (bkTwoThirdsChildScale r) +
        bkScaleRecurrence G d (bkTwoThirdsChildScale r) := by sorry
