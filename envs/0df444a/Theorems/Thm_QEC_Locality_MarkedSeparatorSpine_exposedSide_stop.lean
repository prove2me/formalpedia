-- Prove2me | Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
-- name    : QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:16:35.978455+00:00
-- url     : https://prove2.me/theorems/c4f5612e-e0bc-4499-a25f-9d07a570e9eb
-- title:
--   Marked Separator Spine: exposed Side stop
-- statement:
--   The Marked Separator Spine construction uses the exposed Side stop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L124-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L124-L130

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
    {G : ConnectivityGraph ι} {marked vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right)
    (hminimum : separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
    (hleftLight : 3 * (marked ∩ left).card ≤ 2 * marked.card)
    (hrightLight : 3 * (marked ∩ right).card ≤ 2 * marked.card) :
    (MarkedSeparatorSpine.stop hpartition hminimum hleftLight hrightLight).exposedSide = ∅ := by sorry

attribute [defeq] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
