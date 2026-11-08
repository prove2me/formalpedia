-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
-- name    : QEC.Coding.TannerLiftedProduct.localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:34:14.297669+00:00
-- url     : https://prove2.me/theorems/21f3bb1c-0735-45f7-9722-a89791f1d3e9
-- title:
--   Tanner Lifted Product: local Face Matrix eq local Vertex Coset Leader Matrix of mem agreement
-- statement:
--   Agreement directions are literally rows where the face matrix equals the
--   local product-kernel witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L744-L759
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L744-L759

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
omit [Fintype F] [Fintype G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W)
    (hb : b ∈ localAgreementDirections label h hRank h' c v) :
    ∀ a, localFaceMatrix label c v b a =
      localVertexCosetLeaderMatrix h hRank h' c v b a := by sorry
