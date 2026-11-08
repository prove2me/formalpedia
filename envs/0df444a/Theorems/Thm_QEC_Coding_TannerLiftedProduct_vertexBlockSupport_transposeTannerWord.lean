-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_vertexBlockSupport_transposeTannerWord
-- name    : QEC.Coding.TannerLiftedProduct.vertexBlockSupport_transposeTannerWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:42:06.519127+00:00
-- url     : https://prove2.me/theorems/e0f8d74d-b059-4d9e-92db-1d759864294c
-- title:
--   Tanner Lifted Product: vertex Block Support transpose Tanner Word
-- statement:
--   The Tanner Lifted Product construction uses the vertex Block Support transpose Tanner Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L209-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L209-L241

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.vertexBlockSupport_transposeTannerWord
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    vertexBlockSupport (transposeTannerWord inverseDirection z) =
      (vertexBlockSupport z).map transposeVertexEquiv.toEmbedding := by sorry
