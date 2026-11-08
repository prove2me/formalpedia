-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedValence_qzIncidentFace_card
-- name    : QEC.Coding.BDL26BoundedValence.qzIncidentFace_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:20:54.545039+00:00
-- url     : https://prove2.me/theorems/a6a93b33-65cc-4d4c-8050-f2e83f5d2989
-- title:
--   BDL26 Bounded Valence: qz Incident Face card
-- statement:
--   The exact Q-Z edge face count is the Q vertex's X-direction valence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BoundedValence.lean#L113-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BoundedValence.lean#L113-L116

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare

theorem QEC.Coding.BDL26BoundedValence.qzIncidentFace_card (P : TannerSquarePresentation) (e : QZEdge P) :
    Fintype.card (QZIncidentFace P e) = qXDegree P e.1.1 := by sorry
