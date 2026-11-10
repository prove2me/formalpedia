-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_fiberRegion_disjoint
-- name    : QEC.Coding.BDL26ReplacementSupport.fiberRegion_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:19:07.413272+00:00
-- url     : https://prove2.me/theorems/2e22b160-1960-4ff6-a65f-8a0892f9470f
-- title:
--   BDL26 Replacement Support: fiber Region disjoint
-- statement:
--   The BDL26 Replacement Support construction uses the fiber Region disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L48-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L48-L54

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical
variable {Label Coordinate : Type} [Fintype Label] [Fintype Coordinate]
  [DecidableEq Label] [DecidableEq Coordinate]

theorem QEC.Coding.BDL26ReplacementSupport.fiberRegion_disjoint (owner : Coordinate → Label)
    {first second : Label} (hne : first ≠ second) :
    Disjoint (fiberRegion owner first) (fiberRegion owner second) := by sorry
