-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullRetainedGrowth_retained_card
-- name    : QEC.Coding.BDL26RXIncidenceHullRetainedGrowth.retained_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:38:31.00523+00:00
-- url     : https://prove2.me/theorems/b2802608-09ad-490e-925d-ede15c8c5bbd
-- title:
--   BDL26 RXIncidence Hull Retained Growth: retained card
-- statement:
--   The BDL26 RXIncidence Hull Retained Growth construction uses the retained card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullRetainedGrowth.lean#L109-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullRetainedGrowth.lean#L109-L117

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRZ
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
set_option autoImplicit false
noncomputable section
open QEC.Coding.MultiscaleDecoder QEC.Coding.BDL26IndexedDecoder
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RXIncidenceHullGrowth BDL26RXIncidenceHullSuccessors
open BDL26QuantitativeBounds BDL26RXDifferentialMasks

theorem QEC.Coding.BDL26RXIncidenceHullRetainedGrowth.retained_card (n : Nat) : Fintype.card (Retained n) = 5*2^n := by sorry
