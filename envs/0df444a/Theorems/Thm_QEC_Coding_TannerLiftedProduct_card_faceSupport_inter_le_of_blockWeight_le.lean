-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_faceSupport_inter_le_of_blockWeight_le
-- name    : QEC.Coding.TannerLiftedProduct.card_faceSupport_inter_le_of_blockWeight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:38:43.06433+00:00
-- url     : https://prove2.me/theorems/818b3826-9b0d-472a-99df-bbd80d9c0cec
-- title:
--   Tanner Lifted Product: card face Support inter le of block Weight le
-- statement:
--   If two chains agree away from selected face and vertex blocks, a global
--   block-weight comparison bounds the old affected-face count by the new one
--   plus the number of affected vertex blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1075-L1120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1075-L1120

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
omit [Fintype F] [Group G] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_faceSupport_inter_le_of_blockWeight_le
    (c c' : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (S : Finset (FaceIndex W G)) (T : Finset (VertexIndex G))
    (hface : ∀ p, p ∉ S →
      c' (faceCoordinate (R := R) (R' := R') p) =
        c (faceCoordinate (R := R) (R' := R') p))
    (hvertex : ∀ v, v ∉ T → ∀ r r',
      c' (vertexCoordinate (W := W) v r r') =
        c (vertexCoordinate (W := W) v r r'))
    (hweight : blockWeight c ≤ blockWeight c') :
    (faceSupport c ∩ S).card ≤ (faceSupport c' ∩ S).card + T.card := by sorry
