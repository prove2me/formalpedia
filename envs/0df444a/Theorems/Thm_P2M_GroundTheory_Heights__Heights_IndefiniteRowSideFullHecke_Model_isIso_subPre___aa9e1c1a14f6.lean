-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isIso_subPre___aa9e1c1a14f6
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isIso_subPre___aa9e1c1a14f6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:43.882897+00:00
-- url     : https://prove2.me/theorems/d6e7f963-6151-43b3-bdda-e2a67156884e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model is Iso sub Pre   aa9e1c1a14f6: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model is Iso sub Pre   aa9e1c
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model is Iso sub Pre   aa9e1c1a14f6 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model is Iso sub Pre   aa9e1c1a14f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L150-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L150-L157

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff
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
open CategoryTheory AlgebraicGeometry
variable (X : Scheme.{0})

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isIso_subPre___aa9e1c1a14f6 {a m' : ℕ} (ha : 0 < a) (hm' : 0 < m') :
    IsIso (genRes X a ⁻¹ᵁ subOpen X a m').ι := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«isIso_subPre_ι» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isIso_subPre___aa9e1c1a14f6
