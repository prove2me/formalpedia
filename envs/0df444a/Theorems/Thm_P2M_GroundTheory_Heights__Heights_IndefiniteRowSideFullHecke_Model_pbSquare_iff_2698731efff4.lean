-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_pbSquare_iff_2698731efff4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_pbSquare_iff_2698731efff4
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:57:43.465501+00:00
-- url     : https://prove2.me/theorems/50505e9e-c03a-58f5-97ea-60e8403c0bbd
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model pb Square iff 2698731efff4: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model pb Square iff 2698731efff4
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model pb Square iff 2698731efff4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model pb Square iff 2698731efff4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L98-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L98-L116

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_pbSquare_iff_2698731efff4 {A B C : Scheme.{0}} (q : A ⟶ B) (j : B ⟶ Z) (k : A ⟶ C) (r : C ⟶ Z)
    (hsq : q ≫ j = k ≫ r) (f : (Scheme.Modules.pullback j).obj F ≅ (Scheme.Modules.pullback j).obj G)
    (ψ : (Scheme.Modules.pullback r).obj F ≅ (Scheme.Modules.pullback r).obj G) :
    (Scheme.Modules.pullback q).map f.hom = (pbSquare q j k r hsq F).hom ≫
        (Scheme.Modules.pullback k).map ψ.hom ≫ (pbSquare q j k r hsq G).inv ↔
      along hsq f = along (rfl : k ≫ r = k ≫ r) ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«pbSquare_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_pbSquare_iff_2698731efff4
