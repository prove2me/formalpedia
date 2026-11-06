-- Prove2me | Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_stopSides_disjoint
-- name    : QEC.Locality.MarkedSeparatorSpine.stopSides_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:16:36.404241+00:00
-- url     : https://prove2.me/theorems/0c9b0ef0-d361-4b3b-9ebb-e2e614a1ef46
-- title:
--   Marked Separator Spine: stop Sides disjoint
-- statement:
--   The Marked Separator Spine construction uses the stop Sides disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L254-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L254-L262

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.MarkedSeparatorSpine.stopSides_disjoint
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    Disjoint spine.stopSides.1 spine.stopSides.2 := by sorry
