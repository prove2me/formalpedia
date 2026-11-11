-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_path_mem_of_saturated
-- name    : QEC.Coding.BDL26RXIncidenceHullGrowth.path_mem_of_saturated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:58:14.593193+00:00
-- url     : https://prove2.me/theorems/c481a0bd-4e64-4a70-89e0-f49c5f38be22
-- title:
--   BDL26 RXIncidence Hull Growth: path mem of saturated
-- statement:
--   The BDL26 RXIncidence Hull Growth construction uses the path mem of saturated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L50-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L50-L56

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXIncidenceHullGrowth.path_mem_of_saturated (A : Finset (state S i.val).presentation.Q)
    (closed : IncidenceSaturated S depth i A)
    {q r : (state S i.val).presentation.Q} (hq : q ∈ A)
    (path : SharedZPath (state S i.val).presentation q r) : r ∈ A := by sorry
