-- Prove2me | Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposed_stopSides_separatorUnion
-- name    : QEC.Locality.MarkedSeparatorSpine.exposed_stopSides_separatorUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:43:06.500358+00:00
-- url     : https://prove2.me/theorems/c2df4bcc-3ffe-49e1-bd71-470f32d27529
-- title:
--   Marked Separator Spine: exposed stop Sides separator Union
-- statement:
--   The exposed side, the two terminal sides, and the accumulated separators cover
--   the original spine carrier exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L337-L374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L337-L374

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.MarkedSeparatorSpine.exposed_stopSides_separatorUnion
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.exposedSide ∪ spine.stopSides.1 ∪ spine.stopSides.2 ∪
      markedSpineSeparatorUnion spine = vertices := by sorry
