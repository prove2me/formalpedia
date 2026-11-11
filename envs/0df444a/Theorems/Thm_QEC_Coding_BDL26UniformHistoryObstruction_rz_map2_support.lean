-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_rz_map2_support
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.rz_map2_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:32:57.14004+00:00
-- url     : https://prove2.me/theorems/da65e53f-6f18-4368-9c42-892810526aa3
-- title:
--   BDL26 Uniform History Obstruction: rz map2 support
-- statement:
--   RZ map2 support is exactly the injective image, not a replicated syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L56-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L56-L76

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.rz_map2_support (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (s : Word BDL26Field P.Z) :
    hammingSupport (map2Coord P A S s) =
      (hammingSupport s).image (fun z => (⟨z, rzMap1ZRoot P A z S⟩ : RZZ P S)) := by sorry
