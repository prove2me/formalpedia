-- Prove2me | Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_threeSides_noEdge
-- name    : QEC.Locality.MarkedSeparatorSpine.threeSides_noEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:43:19.587288+00:00
-- url     : https://prove2.me/theorems/856cbdfa-ae04-4c0e-92c5-ee5e9f5d6120
-- title:
--   Marked Separator Spine: three Sides no Edge
-- statement:
--   The Marked Separator Spine construction uses the three Sides no Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L284-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L284-L319

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.MarkedSeparatorSpine.threeSides_noEdge
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    NoEdgeBetween G spine.exposedSide spine.stopSides.1 ∧
      NoEdgeBetween G spine.exposedSide spine.stopSides.2 ∧
      NoEdgeBetween G spine.stopSides.1 spine.stopSides.2 := by sorry
