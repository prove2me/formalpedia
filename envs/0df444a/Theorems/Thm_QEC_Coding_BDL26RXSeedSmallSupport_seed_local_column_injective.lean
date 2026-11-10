-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXSeedSmallSupport_seed_local_column_injective
-- name    : QEC.Coding.BDL26RXSeedSmallSupport.seed_local_column_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:33:19.792909+00:00
-- url     : https://prove2.me/theorems/203cc908-e9c5-4a98-89db-ee4f5f8de37e
-- title:
--   BDL26 RXSeed Small Support: seed local column injective
-- statement:
--   Actual seed RX edge columns are pairwise distinct at every valid scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXSeedSmallSupport.lean#L570-L610
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXSeedSmallSupport.lean#L570-L610

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXSeedSmallSupport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RXSeedSmallSupport.seed_local_column_injective (S : OddScale)
    (x : baseTannerSquarePresentation.X) :
    Function.Injective (fun edge : DoubleCylinderEdge baseTannerSquarePresentation x S =>
      fun face : DoubleCylinderFace baseTannerSquarePresentation x S =>
        doubleCylinderFaceEdgeMatrix baseTannerSquarePresentation x S edge face) := by sorry
