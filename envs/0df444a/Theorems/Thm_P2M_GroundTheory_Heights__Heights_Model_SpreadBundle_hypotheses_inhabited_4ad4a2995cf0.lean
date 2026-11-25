-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadBundle_hypotheses_inhabited_4ad4a2995cf0
-- name    : P2M_GroundTheory_Heights__Heights_Model_SpreadBundle_hypotheses_inhabited_4ad4a2995cf0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:07.027791+00:00
-- url     : https://prove2.me/theorems/973c755c-52ae-4485-82a4-886f1451d382
-- title:
--   P2 M Ground Theory Heights  Heights Model Spread Bundle hypotheses inhabited 4ad4a2995cf0: P2 M Ground Theory Heights  Heights Model Spread Bundle hypotheses inhabited 4ad4a2995cf0
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Spread Bundle hypotheses inhabited 4ad4a2995cf0 construction uses the P2 M Ground Theory Heights  Heights Model Spread Bundle hypotheses inhabited 4ad4a2995cf0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L521-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L521-L523

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

theorem P2M_GroundTheory_Heights__Heights_Model_SpreadBundle_hypotheses_inhabited_4ad4a2995cf0 :
    IsVectorBundle (structureModule (baseChange (𝟙 SpecZ) (ZLoc ⟨2, Nat.prime_two⟩))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SpreadBundle».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_SpreadBundle_hypotheses_inhabited_4ad4a2995cf0
