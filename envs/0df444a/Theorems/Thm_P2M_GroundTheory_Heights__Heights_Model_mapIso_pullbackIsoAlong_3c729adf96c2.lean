-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackIsoAlong_3c729adf96c2
-- name    : P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackIsoAlong_3c729adf96c2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:56.200128+00:00
-- url     : https://prove2.me/theorems/fe0af9f0-e6bf-4142-a4ed-abe5ef84a158
-- title:
--   P2 M Ground Theory Heights  Heights Model map Iso pullback Iso Along 3c729adf96c2: P2 M Ground Theory Heights  Heights Model map Iso pullback Iso Along 3c729adf96c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Model map Iso pullback Iso Along 3c729adf96c2 construction uses the P2 M Ground Theory Heights  Heights Model map Iso pullback Iso Along 3c729adf96c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L99-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L99-L113

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry
noncomputable section
set_option linter.unusedSimpArgs false
universe u
variable {T' T Y Z : Scheme.{u}}

theorem P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackIsoAlong_3c729adf96c2 {W' W O O' : Scheme.{0}} (u : W' ⟶ W) {t : W ⟶ O'} {h : O' ⟶ O}
    {k : W ⟶ O} (ek : t ≫ h = k) {t' : W' ⟶ O'} {k' : W' ⟶ O} (ee : t' ≫ h = k')
    (ut : u ≫ t = t') (uk : u ≫ k = k') {A B : O.Modules}
    (ψ : (Scheme.Modules.pullback h).obj A ≅ (Scheme.Modules.pullback h).obj B) :
    (Scheme.Modules.pullback u).mapIso (pullbackIsoAlong ek ψ) =
      (pullbackCompIso uk (Iso.refl ((Scheme.Modules.pullback k).obj A))).symm ≪≫
        pullbackIsoAlong ee ψ ≪≫ pullbackCompIso uk (Iso.refl _) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mapIso_pullbackIsoAlong» := P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackIsoAlong_3c729adf96c2
