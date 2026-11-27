-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_pbSection_eq_pullSection_586a7923eab1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_pbSection_eq_pullSection_586a7923eab1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:25:55.768978+00:00
-- url     : https://prove2.me/theorems/a65b80c3-8b23-532f-aefc-75286af51c6d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model pb Section eq pull Section 586a7923eab1: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model pb Section eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model pb Section eq pull Section 586a7923eab1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model pb Section eq pull Section 586a7923eab1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsVectorBundleIffModel.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsVectorBundleIffModel.lean#L18-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsVectorBundleIffModel
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
open CategoryTheory Opposite AlgebraicGeometry Limits
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_pbSection_eq_pullSection_586a7923eab1 {A B : Scheme.{0}} (f : A ⟶ B) (M : B.Modules) (t : Γ(M, ⊤)) :
    pbSection f M t = GroundTheory.Heights₂.Heights.Model.pullSection f M t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«pbSection_eq_pullSection» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_pbSection_eq_pullSection_586a7923eab1
