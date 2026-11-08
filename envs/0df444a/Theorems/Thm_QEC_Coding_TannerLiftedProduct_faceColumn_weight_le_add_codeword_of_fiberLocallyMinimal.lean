-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceColumn_weight_le_add_codeword_of_fiberLocallyMinimal
-- name    : QEC.Coding.TannerLiftedProduct.faceColumn_weight_le_add_codeword_of_fiberLocallyMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:34:41.468812+00:00
-- url     : https://prove2.me/theorems/0117f605-39e8-4c0a-bb99-810112e6af08
-- title:
--   Tanner Lifted Product: face Column weight le add codeword of fiber Locally Minimal
-- statement:
--   The preceding column correction bound in the exact parity-check-code
--   interface consumed by the PK22 local-star minimality theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1480-L1499
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1480-L1499

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

theorem QEC.Coding.TannerLiftedProduct.faceColumn_weight_le_add_codeword_of_fiberLocallyMinimal
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (a : W) (delta : Word F W)
    (hdelta : delta ∈
      (ProductExpansion.parityCheckCode
        (ProductExpansion.generatorImageParityCheck g')).carrier) :
    HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a) ≤
      HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a + delta) + 2 := by sorry
