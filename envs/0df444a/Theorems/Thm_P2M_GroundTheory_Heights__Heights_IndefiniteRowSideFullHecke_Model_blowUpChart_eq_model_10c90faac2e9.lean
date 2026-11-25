-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_blowUpChart_eq_model_10c90faac2e9
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_blowUpChart_eq_model_10c90faac2e9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:24:58.021691+00:00
-- url     : https://prove2.me/theorems/e7189a4d-11c4-500c-afee-c24b05f38a4d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model blow Up Chart eq model 10c90faac2e9: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model blow Up Chart eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model blow Up Chart eq model 10c90faac2e9 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model blow Up Chart eq model 10c90faac2e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ComapEqMaximalIdeal.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ComapEqMaximalIdeal.lean#L8-L10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ComapEqMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_blowUpChart_eq_model_10c90faac2e9 {A K : Type} [CommRing A] [Field K] [Algebra A K] {n : ℕ}
    (x : Fin n → A) (i : Fin n) :
    _root_.GroundTheory.Heights₂.Heights.Model.blowUpChart K x i = blowUpChart A K x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«blowUpChart_eq_model» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_blowUpChart_eq_model_10c90faac2e9
