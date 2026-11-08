-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceColumn_weight_le_add_generator_of_fiberLocallyMinimal
-- name    : QEC.Coding.TannerLiftedProduct.faceColumn_weight_le_add_generator_of_fiberLocallyMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:39:39.678249+00:00
-- url     : https://prove2.me/theorems/da655c4d-d328-4cb0-ae8d-da7cfb3af296
-- title:
--   Tanner Lifted Product: face Column weight le add generator of fiber Locally Minimal
-- statement:
--   Source-level local minimality says that correcting any one face column by
--   a generated second-code word can decrease its face weight by at most the two
--   vertex blocks at the edge endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1434-L1476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1434-L1476

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.faceColumn_weight_le_add_generator_of_fiberLocallyMinimal
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (a : W) (u : Word F R') :
    HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a) ≤
      HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a +
          g'.transpose.mulVec u) + 2 := by sorry
