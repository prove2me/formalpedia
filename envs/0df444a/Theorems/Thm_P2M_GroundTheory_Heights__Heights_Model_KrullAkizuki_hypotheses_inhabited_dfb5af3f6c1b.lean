-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_hypotheses_inhabited_dfb5af3f6c1b
-- name    : P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_hypotheses_inhabited_dfb5af3f6c1b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:11.886381+00:00
-- url     : https://prove2.me/theorems/54fa0d08-723d-4617-b3a6-963dabcf73e7
-- title:
--   P2 M Ground Theory Heights  Heights Model Krull Akizuki hypotheses inhabited dfb5af3f6c1b: P2 M Ground Theory Heights  Heights Model Krull Akizuki hypotheses inhabited dfb5af3f6c1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Krull Akizuki hypotheses inhabited dfb5af3f6c1b construction uses the P2 M Ground Theory Heights  Heights Model Krull Akizuki hypotheses inhabited dfb5af3f6c1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L479-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L479-L483

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
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
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_hypotheses_inhabited_dfb5af3f6c1b :
    IsNoetherianRing ℤ ∧ ringKrullDim ℤ = 1 ∧ IsFractionRing ℤ ℚ ∧ FiniteDimensional ℚ ℚ ∧
      IsScalarTower ℤ ℚ ℚ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«KrullAkizuki».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_hypotheses_inhabited_dfb5af3f6c1b
