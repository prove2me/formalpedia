-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_invOpen_le_of_dvd__4378c74e8fc8
-- name    : P2M_GroundTheory_Heights__Heights_Model_invOpen_le_of_dvd__4378c74e8fc8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:44.569634+00:00
-- url     : https://prove2.me/theorems/bc675ce5-7026-49d8-99ae-088e402e431f
-- title:
--   P2 M Ground Theory Heights  Heights Model inv Open le of dvd  4378c74e8fc8: P2 M Ground Theory Heights  Heights Model inv Open le of dvd  4378c74e8fc8
-- statement:
--   The P2 M Ground Theory Heights  Heights Model inv Open le of dvd  4378c74e8fc8 construction uses the P2 M Ground Theory Heights  Heights Model inv Open le of dvd  4378c74e8fc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L25-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueBundles
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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}

theorem P2M_GroundTheory_Heights__Heights_Model_invOpen_le_of_dvd__4378c74e8fc8 (f : X ⟶ SpecZ) {a b : ℤ} (h : a ∣ b) : invOpen f b ≤ invOpen f a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«invOpen_le_of_dvd'» := P2M_GroundTheory_Heights__Heights_Model_invOpen_le_of_dvd__4378c74e8fc8
