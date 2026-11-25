-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_hom_46c147a3a660
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_hom_46c147a3a660
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:52:56.896623+00:00
-- url     : https://prove2.me/theorems/18045726-d1d6-4fa5-8563-0f02482f2a89
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along hom 46c147a3a660: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along hom 46c147a3a660
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along hom 46c147a3a660 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model along hom 46c147a3a660 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L16-L21

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_hom_46c147a3a660 {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    (along e ψ).hom = (Scheme.Modules.pullbackCongr e).inv.app F ≫
      (Scheme.Modules.pullbackComp g h).inv.app F ≫ (Scheme.Modules.pullback g).map ψ.hom ≫
        (Scheme.Modules.pullbackComp g h).hom.app G ≫ (Scheme.Modules.pullbackCongr e).hom.app G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«along_hom» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_hom_46c147a3a660
