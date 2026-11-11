-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_pathUnion_saturated
-- name    : QEC.Coding.BDL26RXIncidenceHullGrowth.pathUnion_saturated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:59:08.671182+00:00
-- url     : https://prove2.me/theorems/88ece6f7-b8fc-4a04-87b3-8b5ef5a174fa
-- title:
--   BDL26 RXIncidence Hull Growth: path Union saturated
-- statement:
--   The BDL26 RXIncidence Hull Growth construction uses the path Union saturated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L58-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L58-L62

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXIncidenceHullGrowth.pathUnion_saturated (seed : Finset (state S i.val).presentation.Q) :
    IncidenceSaturated S depth i (pathUnion S depth i seed) := by sorry
