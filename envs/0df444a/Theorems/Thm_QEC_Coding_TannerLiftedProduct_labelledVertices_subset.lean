-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_labelledVertices_subset
-- name    : QEC.Coding.TannerLiftedProduct.labelledVertices_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:40:31.767292+00:00
-- url     : https://prove2.me/theorems/fcd3285c-d2fc-4556-8991-35d4bbf5fbe3
-- title:
--   Tanner Lifted Product: labelled Vertices subset
-- statement:
--   The canonical labelled set is contained in every closed labelled set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L460-L467
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L460-L467

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.labelledVertices_subset (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) (L : Finset (VertexIndex G))
    (hL : IsClosedLabelledSet label c m L) :
    labelledVertices label c m ⊆ L := by sorry
