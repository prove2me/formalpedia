-- Prove2me | Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_subset
-- name    : QEC.Locality.MarkedSeparatorSpine.exposedSide_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:16:48.804202+00:00
-- url     : https://prove2.me/theorems/dde3e6bf-8bbc-42dc-978b-3660145b6868
-- title:
--   Marked Separator Spine: exposed Side subset
-- statement:
--   The Marked Separator Spine construction uses the exposed Side subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L164-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L164-L175

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.MarkedSeparatorSpine.exposedSide_subset
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.exposedSide ⊆ vertices := by sorry
