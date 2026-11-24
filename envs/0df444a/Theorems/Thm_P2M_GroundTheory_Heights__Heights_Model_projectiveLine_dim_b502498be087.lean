-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_projectiveLine_dim_b502498be087
-- name    : P2M_GroundTheory_Heights__Heights_Model_projectiveLine_dim_b502498be087
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:40.257093+00:00
-- url     : https://prove2.me/theorems/3b6f11ab-ec3a-4c38-894f-ccb14314ebd4
-- title:
--   P2 M Ground Theory Heights  Heights Model projective Line dim b502498be087: P2 M Ground Theory Heights  Heights Model projective Line dim b502498be087
-- statement:
--   The P2 M Ground Theory Heights  Heights Model projective Line dim b502498be087 construction uses the P2 M Ground Theory Heights  Heights Model projective Line dim b502498be087 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L573-L582
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L573-L582

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

theorem P2M_GroundTheory_Heights__Heights_Model_projectiveLine_dim_b502498be087 :
    ringKrullDim (MRing (fun _ : Unit => Fin 2) ℚ ⧸ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ))) =
      ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«projectiveLine_dim» := P2M_GroundTheory_Heights__Heights_Model_projectiveLine_dim_b502498be087
