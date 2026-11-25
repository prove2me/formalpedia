-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FiniteNormalization_hypotheses_inhabited_edb5f88a8d5d
-- name    : P2M_GroundTheory_Heights__Heights_Model_FiniteNormalization_hypotheses_inhabited_edb5f88a8d5d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:32:07.837962+00:00
-- url     : https://prove2.me/theorems/fd0c0380-380d-4a04-93bc-8f1d04298b79
-- title:
--   P2 M Ground Theory Heights  Heights Model Finite Normalization hypotheses inhabited edb5f88a8d5d: P2 M Ground Theory Heights  Heights Model Finite Normalization hypotheses inhabited edb5f88a8d5d
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Finite Normalization hypotheses inhabited edb5f88a8d5d construction uses the P2 M Ground Theory Heights  Heights Model Finite Normalization hypotheses inhabited edb5f88a8d5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L646-L649
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L646-L649

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

theorem P2M_GroundTheory_Heights__Heights_Model_FiniteNormalization_hypotheses_inhabited_edb5f88a8d5d :
    IsIntegral SpecZ ∧ LocallyOfFiniteType (𝟙 SpecZ) ∧ QuasiCompact (𝟙 SpecZ) ∧
      FiniteDimensional SpecZ.functionField SpecZ.functionField := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«FiniteNormalization».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_FiniteNormalization_hypotheses_inhabited_edb5f88a8d5d
