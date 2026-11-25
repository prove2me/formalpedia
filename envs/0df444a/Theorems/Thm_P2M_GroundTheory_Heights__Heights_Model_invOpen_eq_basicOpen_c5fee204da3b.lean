-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_invOpen_eq_basicOpen_c5fee204da3b
-- name    : P2M_GroundTheory_Heights__Heights_Model_invOpen_eq_basicOpen_c5fee204da3b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:33.849818+00:00
-- url     : https://prove2.me/theorems/b4c17e5a-c1d9-4549-9ca9-d0630dd46650
-- title:
--   P2 M Ground Theory Heights  Heights Model inv Open eq basic Open c5fee204da3b: P2 M Ground Theory Heights  Heights Model inv Open eq basic Open c5fee204da3b
-- statement:
--   The P2 M Ground Theory Heights  Heights Model inv Open eq basic Open c5fee204da3b construction uses the P2 M Ground Theory Heights  Heights Model inv Open eq basic Open c5fee204da3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericSections.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericSections.lean#L50-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
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
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Model_invOpen_eq_basicOpen_c5fee204da3b {X : Scheme.{0}} (f : X ⟶ SpecZ) (k : ℤ) :
    invOpen f k = X.basicOpen ((k : Γ(X, f ⁻¹ᵁ ⊤))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«invOpen_eq_basicOpen» := P2M_GroundTheory_Heights__Heights_Model_invOpen_eq_basicOpen_c5fee204da3b
