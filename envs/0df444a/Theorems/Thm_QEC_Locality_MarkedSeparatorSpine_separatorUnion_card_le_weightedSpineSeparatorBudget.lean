-- Prove2me | Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_separatorUnion_card_le_weightedSpineSeparatorBudget
-- name    : QEC.Locality.MarkedSeparatorSpine.separatorUnion_card_le_weightedSpineSeparatorBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:43:18.657606+00:00
-- url     : https://prove2.me/theorems/ec64c99c-fc33-4786-9d3e-368abbe8816d
-- title:
--   Marked Separator Spine: separator Union card le weighted Spine Separator Budget
-- statement:
--   The Marked Separator Spine construction uses the separator Union card le weighted Spine Separator Budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L537-L554
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean#L537-L554

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.MarkedSeparatorSpine.separatorUnion_card_le_weightedSpineSeparatorBudget
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices)
    {beta exponent : ℝ}
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hvertices : 1 ≤ vertices.card) {r : Nat} (hcard : vertices.card ≤ r) :
    (markedSpineSeparatorUnion spine).card ≤
      weightedSpineSeparatorBudget beta exponent r := by sorry
