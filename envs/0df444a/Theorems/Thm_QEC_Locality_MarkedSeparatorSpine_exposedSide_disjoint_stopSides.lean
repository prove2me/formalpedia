-- Prove2me | Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_disjoint_stopSides
-- name    : QEC.Locality.MarkedSeparatorSpine.exposedSide_disjoint_stopSides
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:01.219325+00:00
-- url     : https://prove2.me/theorems/034b9a17-f8d1-46e9-86a9-845a9ec6794e
-- title:
--   Marked Separator Spine: exposed Side disjoint stop Sides
-- statement:
--   The Marked Separator Spine construction uses the exposed Side disjoint stop Sides property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L264-L272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L264-L272

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.MarkedSeparatorSpine.exposedSide_disjoint_stopSides
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    Disjoint spine.exposedSide spine.stopSides.1 ∧
      Disjoint spine.exposedSide spine.stopSides.2 := by sorry
