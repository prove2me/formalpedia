-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_base_nonempty_hull_card
-- name    : QEC.Coding.BDL26RXIncidenceHullGrowth.base_nonempty_hull_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T22:39:51.115328+00:00
-- url     : https://prove2.me/theorems/d2d30a4f-57ec-4353-aad9-d6b73cb912fc
-- title:
--   BDL26 RXIncidence Hull Growth: base nonempty hull card
-- statement:
--   The BDL26 RXIncidence Hull Growth construction uses the base nonempty hull card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L141-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L141-L144

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXIncidenceHullGrowth.base_nonempty_hull_card (seed : Finset BaseQubit) (hne : seed.Nonempty)
    (hd : 0 < depth) : (incidenceHull S depth ⟨0,hd⟩ seed).card = 5 := by sorry
