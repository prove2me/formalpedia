-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzSharedQ_sum_eq_face_corners
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzSharedQ_sum_eq_face_corners
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:40:19.595237+00:00
-- url     : https://prove2.me/theorems/117402ab-7218-4b49-a31b-a7e0d512d20b
-- title:
--   BDL26 Replacement Cochain Maps: rz Shared Q sum eq face corners
-- statement:
--   Perfect pairing reindexes any shared-Q sum by the two corners of each
--   old face.  This is the original presentation equivalence, not a selected face.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1608-L1628
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1608-L1628

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzSharedQ_sum_eq_face_corners
    (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    {Index : Type} (value : P.Q → Word Field Index) :
    (∑ q : P.Q, if P.xq x q && P.qz q z then value q else 0) =
      ∑ owner : RZOldFaceOver P x z, ∑ corner : Two,
        value (P.faceQ owner.1 corner) := by sorry
