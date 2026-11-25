-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadIso_hypotheses_inhabited_370230db64ce
-- name    : P2M_GroundTheory_Heights__Heights_Model_SpreadIso_hypotheses_inhabited_370230db64ce
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:54.608832+00:00
-- url     : https://prove2.me/theorems/2387843c-2d63-4ae3-aebf-89070ade03b4
-- title:
--   P2 M Ground Theory Heights  Heights Model Spread Iso hypotheses inhabited 370230db64ce: P2 M Ground Theory Heights  Heights Model Spread Iso hypotheses inhabited 370230db64ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Spread Iso hypotheses inhabited 370230db64ce construction uses the P2 M Ground Theory Heights  Heights Model Spread Iso hypotheses inhabited 370230db64ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L525-L531
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L525-L531

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

theorem P2M_GroundTheory_Heights__Heights_Model_SpreadIso_hypotheses_inhabited_370230db64ce :
    IsVectorBundle (structureModule (invOpen (𝟙 SpecZ) (1 : ℕ) : Scheme.{0})) ∧
      Nonempty ((Scheme.Modules.pullback (toInvOpen (𝟙 SpecZ) ℚ (1 : ℕ)
        (isUnit_intCast_rat 1 one_ne_zero))).obj (structureModule _) ≅
        (Scheme.Modules.pullback (toInvOpen (𝟙 SpecZ) ℚ (1 : ℕ)
        (isUnit_intCast_rat 1 one_ne_zero))).obj (structureModule _)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SpreadIso».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_SpreadIso_hypotheses_inhabited_370230db64ce
