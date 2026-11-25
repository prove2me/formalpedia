-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DominatingDVR_hypotheses_inhabited_a5ce5cb27335
-- name    : P2M_GroundTheory_Heights__Heights_Model_DominatingDVR_hypotheses_inhabited_a5ce5cb27335
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:25.846726+00:00
-- url     : https://prove2.me/theorems/8bdc55ec-2721-4551-a721-e0acff557ef3
-- title:
--   P2 M Ground Theory Heights  Heights Model Dominating DVR hypotheses inhabited a5ce5cb27335: P2 M Ground Theory Heights  Heights Model Dominating DVR hypotheses inhabited a5ce5cb27335
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Dominating DVR hypotheses inhabited a5ce5cb27335 construction uses the P2 M Ground Theory Heights  Heights Model Dominating DVR hypotheses inhabited a5ce5cb27335 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L457-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L457-L461

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

theorem P2M_GroundTheory_Heights__Heights_Model_DominatingDVR_hypotheses_inhabited_a5ce5cb27335 :
    IsDomain ℤ_[2] ∧ IsNoetherianRing ℤ_[2] ∧ IsLocalRing ℤ_[2] ∧ ¬ IsField ℤ_[2] ∧
      IsFractionRing ℤ_[2] ℚ_[2] := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«DominatingDVR».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_DominatingDVR_hypotheses_inhabited_a5ce5cb27335
