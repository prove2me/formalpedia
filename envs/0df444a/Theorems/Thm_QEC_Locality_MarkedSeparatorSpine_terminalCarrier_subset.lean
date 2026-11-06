-- Prove2me | Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_terminalCarrier_subset
-- name    : QEC.Locality.MarkedSeparatorSpine.terminalCarrier_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:16:29.308341+00:00
-- url     : https://prove2.me/theorems/de9782c4-5d06-4a5e-b879-5e904dc2aed5
-- title:
--   Marked Separator Spine: terminal Carrier subset
-- statement:
--   The Marked Separator Spine construction uses the terminal Carrier subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L153-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L153-L162

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.MarkedSeparatorSpine.terminalCarrier_subset
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.terminalCarrier ⊆ vertices := by sorry
