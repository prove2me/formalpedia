-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_mem_pathUnion
-- name    : QEC.Coding.BDL26RXIncidenceHullGrowth.mem_pathUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:42:03.330499+00:00
-- url     : https://prove2.me/theorems/35ff4169-9822-4cd7-a627-ed5fccdde58a
-- title:
--   BDL26 RXIncidence Hull Growth: mem path Union
-- statement:
--   The BDL26 RXIncidence Hull Growth construction uses the mem path Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L44-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L44-L48

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXIncidenceHullGrowth.mem_pathUnion (seed : Finset (state S i.val).presentation.Q)
    (r : (state S i.val).presentation.Q) :
    r ∈ pathUnion S depth i seed ↔
      ∃ q ∈ seed, SharedZPath (state S i.val).presentation q r := by sorry
