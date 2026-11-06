-- Prove2me | Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_stopSides_marked_light
-- name    : QEC.Locality.MarkedSeparatorSpine.stopSides_marked_light
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:16:45.021854+00:00
-- url     : https://prove2.me/theorems/559af35d-9804-46be-8d73-527596c110b6
-- title:
--   Marked Separator Spine: stop Sides marked light
-- statement:
--   The Marked Separator Spine construction uses the stop Sides marked light property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L561-L572
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L561-L572

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.MarkedSeparatorSpine.stopSides_marked_light
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    3 * (marked ∩ spine.stopSides.1).card ≤ 2 * marked.card ∧
      3 * (marked ∩ spine.stopSides.2).card ≤ 2 * marked.card := by sorry
