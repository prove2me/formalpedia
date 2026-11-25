-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_assoc_b3f71914056c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_assoc_b3f71914056c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:52:39.366688+00:00
-- url     : https://prove2.me/theorems/b18907a7-d9d8-47f5-81d6-025901378a12
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along assoc b3f71914056c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along assoc b3f71914056c
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along assoc b3f71914056c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along assoc b3f71914056c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L53-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L53-L87

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_assoc_b3f71914056c {p : T' ⟶ T} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} {k' : T' ⟶ Z}
    (e : g ≫ h = k) (e' : p ≫ k = k') (e'' : (p ≫ g) ≫ h = k')
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    along e' (along e ψ) = along e'' ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«along_assoc» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_assoc_b3f71914056c
