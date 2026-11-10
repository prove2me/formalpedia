-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_grid_cleanup
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_grid_cleanup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:26:28.742369+00:00
-- url     : https://prove2.me/theorems/9122c8ae-3e43-45ea-bc93-aacbf939aa92
-- title:
--   BDL26 RXLocal Replacement: x Local grid cleanup
-- statement:
--   An arbitrary syndrome inside one square region can be reduced to its
--   root parity using concrete cylinder edges with zero connecting-map cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L539-L553
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L539-L553

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_grid_cleanup
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (copy : Two)
    (root : GridVertex S.half) (syndrome : Word Field (GridVertex S.half)) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f =
        xLocalWordPush (fun ij : GridVertex S.half => Sum.inl (copy, face, ij))
          (syndrome + Pi.single root (totalParity syndrome)) ∧
      connectingWeight P A x S f = 0 := by sorry
