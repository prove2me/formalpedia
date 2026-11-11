-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_incidenceHull_eq_pathUnion
-- name    : QEC.Coding.BDL26RXIncidenceHullGrowth.incidenceHull_eq_pathUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:59:37.322387+00:00
-- url     : https://prove2.me/theorems/12a97144-e51e-4656-9d4c-76458e6ab244
-- title:
--   BDL26 RXIncidence Hull Growth: incidence Hull eq path Union
-- statement:
--   Equality to the EXISTING least saturated hull, in both directions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L65-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L65-L75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXIncidenceHullGrowth.incidenceHull_eq_pathUnion (seed : Finset (state S i.val).presentation.Q) :
    incidenceHull S depth i seed = pathUnion S depth i seed := by sorry
