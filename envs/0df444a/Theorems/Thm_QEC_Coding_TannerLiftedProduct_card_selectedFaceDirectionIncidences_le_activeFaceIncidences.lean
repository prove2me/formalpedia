-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_selectedFaceDirectionIncidences_le_activeFaceIncidences
-- name    : QEC.Coding.TannerLiftedProduct.card_selectedFaceDirectionIncidences_le_activeFaceIncidences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:02:43.850977+00:00
-- url     : https://prove2.me/theorems/a824966f-c0ce-4967-91e1-61028555f5f4
-- title:
--   Tanner Lifted Product: card selected Face Direction Incidences le active Face Incidences
-- statement:
--   Selected direction incidences inject into the global active-face
--   incidence set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L483-L523
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L483-L523

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
omit [Fintype F] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_selectedFaceDirectionIncidences_le_activeFaceIncidences
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) :
    (selectedFaceDirectionIncidences label c m).card ≤
      (activeFaceIncidences label c (labelledVertices label c m)).card := by sorry
