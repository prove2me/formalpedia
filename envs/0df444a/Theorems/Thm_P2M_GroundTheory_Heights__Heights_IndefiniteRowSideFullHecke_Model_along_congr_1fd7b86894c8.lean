-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_congr_1fd7b86894c8
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_congr_1fd7b86894c8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:59.015271+00:00
-- url     : https://prove2.me/theorems/d130621f-cb51-4f17-ad7c-e17467e0e530
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along congr 1fd7b86894c8: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along congr 1fd7b86894c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along congr 1fd7b86894c8 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along congr 1fd7b86894c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L23-L27

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
variable {T T' Y Z : Scheme.{0}} {F G : Z.Modules}
local notation "along" => GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_congr_1fd7b86894c8 {g₁ g₂ : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e₁ : g₁ ≫ h = k) (e₂ : g₂ ≫ h = k)
    (hg : g₁ = g₂)
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    along e₁ ψ = along e₂ ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«along_congr» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_congr_1fd7b86894c8
