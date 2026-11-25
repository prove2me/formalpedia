-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_cancel_f626b308d17b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_cancel_f626b308d17b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:53:00.185241+00:00
-- url     : https://prove2.me/theorems/9cdec417-f60c-4783-9910-170655172307
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along cancel f626b308d17b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along cancel f626b308d17b
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along cancel f626b308d17b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along cancel f626b308d17b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L89-L96

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_cancel_f626b308d17b {ρ : T' ⟶ T} [IsIso ρ] {k : T ⟶ Z} {k' : T' ⟶ Z} (e : ρ ≫ k = k')
    {φ₁ φ₂ : (Scheme.Modules.pullback k).obj F ≅ (Scheme.Modules.pullback k).obj G}
    (H : along e φ₁ = along e φ₂) : φ₁ = φ₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«along_cancel» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_cancel_f626b308d17b
