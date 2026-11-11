-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_rz_root_injective
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.rz_root_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:33:04.822631+00:00
-- url     : https://prove2.me/theorems/1135c8ea-72b9-4112-9df2-6cd5df50d70f
-- title:
--   BDL26 Uniform History Obstruction: rz root injective
-- statement:
--   Every RZ syndrome coordinate is sent to one distinct labelled root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L49-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L49-L53

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.rz_root_injective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    Function.Injective (fun z : P.Z => (⟨z, rzMap1ZRoot P A z S⟩ : RZZ P S)) := by sorry
