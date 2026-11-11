-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_combine_full_words
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.combine_full_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:08:12.770041+00:00
-- url     : https://prove2.me/theorems/844d65c5-6939-4178-bee9-540711dbb4a5
-- title:
--   BDL26 History Error Telescoping: combine full words
-- statement:
--   The BDL26 History Error Telescoping construction uses the combine full words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L40-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L40-L51

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w

theorem QEC.Coding.BDL26HistoryErrorTelescoping.combine_full_words {I : Type u} {J : Type v} {K : Type w}
    (f : Word BDL26Field I →ₗ[BDL26Field] Word BDL26Field J)
    (g : Word BDL26Field K →ₗ[BDL26Field] Word BDL26Field J)
    (u e d d' : Word BDL26Field J) (y y' : Word BDL26Field I)
    (p p' : Word BDL26Field K)
    (h : f y=u+d+g p) (h' : f y'=u+e+d'+g p') :
    e+d+d'=f (y+y')+g (p+p') := by sorry
