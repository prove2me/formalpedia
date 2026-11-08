-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_activeFaceIncidences_le_four_mul
-- name    : QEC.Coding.TannerLiftedProduct.card_activeFaceIncidences_le_four_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:02:39.808479+00:00
-- url     : https://prove2.me/theorems/0b596b9d-1ef8-4f73-b2ee-c4fc72271f68
-- title:
--   Tanner Lifted Product: card active Face Incidences le four mul
-- statement:
--   An active face has at most four incident product vertices, one for each
--   pair of double-cover side bits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L394-L432
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L394-L432

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_activeFaceIncidences_le_four_mul
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G)) :
    (activeFaceIncidences label c L).card ≤ 4 * (faceSupport c).card := by sorry
