-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_spreadIso_model_iff_eee980e8fcc9
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_spreadIso_model_iff_eee980e8fcc9
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:00:10.269716+00:00
-- url     : https://prove2.me/theorems/6531dc38-28b7-578d-a76d-d3fa95596410
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model spread Iso model iff eee980e8fcc9: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model spread Iso model if
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model spread Iso model iff eee980e8fcc9 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model spread Iso model iff eee980e8fcc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L190-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L190-L229

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
local notation "along" => GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_spreadIso_model_iff_eee980e8fcc9 : GroundTheory.Heights₂.Heights.Model.SpreadIso.Statement ↔
    ∀ (X : Scheme.{0}), IsFiniteTypeOverZ X → ∀ (a : ℕ), 0 < a →
    ∀ (F G : (invOpen X a).toScheme.Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ (t : genFib X ⟶ (invOpen X a).toScheme), t ≫ (invOpen X a).ι = genTo X →
    ∀ α : (Scheme.Modules.pullback t).obj F ≅ (Scheme.Modules.pullback t).obj G,
    ∃ m' : ℕ, 0 < m' ∧ ∃ ψ : (Scheme.Modules.pullback (X.homOfLE (invOpen_le X a m'))).obj F ≅
        (Scheme.Modules.pullback (X.homOfLE (invOpen_le X a m'))).obj G,
      ∀ (t' : genFib X ⟶ (invOpen X (a * m')).toScheme)
        (e : t' ≫ X.homOfLE (invOpen_le X a m') = t), along e ψ = α := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«spreadIso_model_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_spreadIso_model_iff_eee980e8fcc9
