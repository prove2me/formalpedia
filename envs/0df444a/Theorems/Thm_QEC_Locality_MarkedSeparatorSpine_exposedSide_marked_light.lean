-- Prove2me | Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_marked_light
-- name    : QEC.Locality.MarkedSeparatorSpine.exposedSide_marked_light
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:16:47.348483+00:00
-- url     : https://prove2.me/theorems/935931d5-e655-4a23-8431-4fea2ebf63ef
-- title:
--   Marked Separator Spine: exposed Side marked light
-- statement:
--   The aggregate exposed side is marked-light (in fact, below one third).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L220-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L220-L241

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.MarkedSeparatorSpine.exposedSide_marked_light
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    3 * (marked ∩ spine.exposedSide).card ≤ 2 * marked.card := by sorry
