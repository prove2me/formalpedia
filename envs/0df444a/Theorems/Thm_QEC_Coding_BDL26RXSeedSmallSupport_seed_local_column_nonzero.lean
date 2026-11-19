-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXSeedSmallSupport_seed_local_column_nonzero
-- name    : QEC.Coding.BDL26RXSeedSmallSupport.seed_local_column_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:24:24.443735+00:00
-- url     : https://prove2.me/theorems/14a2c2db-ae31-4275-ba4a-f5d6f03d472c
-- title:
--   BDL26 RXSeed Small Support: seed local column nonzero
-- statement:
--   Every actual local edge is incident to an actual local face.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXSeedSmallSupport.lean#L74-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXSeedSmallSupport.lean#L74-L94

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXSeedSmallSupport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RXSeedSmallSupport.seed_local_column_nonzero (S : OddScale) (x : baseTannerSquarePresentation.X)
    (edge : DoubleCylinderEdge baseTannerSquarePresentation x S) :
    ∃ face : DoubleCylinderFace baseTannerSquarePresentation x S,
      doubleCylinderFaceEdgeMatrix baseTannerSquarePresentation x S edge face = 1 := by sorry
