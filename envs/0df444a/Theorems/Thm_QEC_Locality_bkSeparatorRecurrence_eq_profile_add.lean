-- Prove2me | Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_eq_profile_add
-- name    : QEC.Locality.bkSeparatorRecurrence_eq_profile_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:04:13.261193+00:00
-- url     : https://prove2.me/theorems/80d9eaaa-c6b1-4b19-970c-7ade961e7b96
-- title:
--   Locality: bk Separator Recurrence eq profile add
-- statement:
--   The Locality construction uses the bk Separator Recurrence eq profile add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L134-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L134-L142

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

theorem QEC.Locality.bkSeparatorRecurrence_eq_profile_add
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι)
    (hterminal : ¬bkSeparatorTerminal d vertices) :
    bkSeparatorRecurrence G d vertices =
      twoThirdsSeparationProfile G vertices.card +
        bkSeparatorRecurrence G d (measuredTwoThirdsLeft G vertices) +
        bkSeparatorRecurrence G d (measuredTwoThirdsRight G vertices) := by sorry
