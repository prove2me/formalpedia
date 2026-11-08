-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_vertexBlockSupport_iff_localVertexMatrix_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.mem_vertexBlockSupport_iff_localVertexMatrix_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:35:57.117408+00:00
-- url     : https://prove2.me/theorems/4467e903-7d7d-49e1-87a1-a26766d42ab4
-- title:
--   Tanner Lifted Product: mem vertex Block Support iff local Vertex Matrix ne zero
-- statement:
--   A vertex is active exactly when its local coefficient matrix is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L879-L895
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L879-L895

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
omit [Fintype F] [Group G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.mem_vertexBlockSupport_iff_localVertexMatrix_ne_zero
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    v ∈ vertexBlockSupport c ↔ localVertexMatrix c v ≠ 0 := by sorry
