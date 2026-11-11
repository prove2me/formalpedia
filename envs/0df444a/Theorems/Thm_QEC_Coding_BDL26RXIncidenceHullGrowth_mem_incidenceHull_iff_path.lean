-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_mem_incidenceHull_iff_path
-- name    : QEC.Coding.BDL26RXIncidenceHullGrowth.mem_incidenceHull_iff_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:40:21.857835+00:00
-- url     : https://prove2.me/theorems/4d2cba48-969f-4340-bcb9-f96a36f11923
-- title:
--   BDL26 RXIncidence Hull Growth: mem incidence Hull iff path
-- statement:
--   The BDL26 RXIncidence Hull Growth construction uses the mem incidence Hull iff path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L77-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L77-L82

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXIncidenceHullGrowth.mem_incidenceHull_iff_path (seed : Finset (state S i.val).presentation.Q)
    (r : (state S i.val).presentation.Q) :
    r ∈ incidenceHull S depth i seed ↔
      ∃ q ∈ seed, SharedZPath (state S i.val).presentation q r := by sorry
