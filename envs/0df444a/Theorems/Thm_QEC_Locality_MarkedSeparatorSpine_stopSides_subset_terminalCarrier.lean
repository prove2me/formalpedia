-- Prove2me | Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_stopSides_subset_terminalCarrier
-- name    : QEC.Locality.MarkedSeparatorSpine.stopSides_subset_terminalCarrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:16:28.836626+00:00
-- url     : https://prove2.me/theorems/6ebf3980-1a4a-44b3-abc6-6e71f9aab304
-- title:
--   Marked Separator Spine: stop Sides subset terminal Carrier
-- statement:
--   The Marked Separator Spine construction uses the stop Sides subset terminal Carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L243-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L243-L252

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.MarkedSeparatorSpine.stopSides_subset_terminalCarrier
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.stopSides.1 ⊆ spine.terminalCarrier ∧
      spine.stopSides.2 ⊆ spine.terminalCarrier := by sorry
