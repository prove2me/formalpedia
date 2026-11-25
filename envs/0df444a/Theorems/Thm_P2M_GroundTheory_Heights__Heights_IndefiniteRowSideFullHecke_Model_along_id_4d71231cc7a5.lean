-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_id_4d71231cc7a5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_id_4d71231cc7a5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:52:44.775035+00:00
-- url     : https://prove2.me/theorems/080c1998-92e9-44a6-96d1-c26e9b12c821
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along id 4d71231cc7a5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along id 4d71231cc7a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along id 4d71231cc7a5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along id 4d71231cc7a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L29-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L29-L51

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_id_4d71231cc7a5 {g : Y ⟶ Y} {h : Y ⟶ Z} (hg : g = 𝟙 Y) (e : g ≫ h = h)
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    along e ψ = ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«along_id» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_id_4d71231cc7a5
