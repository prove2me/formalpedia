-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SumCp_hypotheses_inhabited_4ffa720a0d9f
-- name    : P2M_GroundTheory_Heights__Heights_Model_SumCp_hypotheses_inhabited_4ffa720a0d9f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:17.730542+00:00
-- url     : https://prove2.me/theorems/53a3b845-3cf4-4ee7-a053-be311ef2ea06
-- title:
--   P2 M Ground Theory Heights  Heights Model Sum Cp hypotheses inhabited 4ffa720a0d9f: P2 M Ground Theory Heights  Heights Model Sum Cp hypotheses inhabited 4ffa720a0d9f
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Sum Cp hypotheses inhabited 4ffa720a0d9f construction uses the P2 M Ground Theory Heights  Heights Model Sum Cp hypotheses inhabited 4ffa720a0d9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L631-L639
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L631-L639

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

theorem P2M_GroundTheory_Heights__Heights_Model_SumCp_hypotheses_inhabited_4ffa720a0d9f :
    (6 : ℤ) ≠ 0 ∧ (2 : ℝ) ≤ 2 ∧
      ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime ∧ ((p : ℝ) ≤ 2 ∨ (p : ℤ) ∣ 6) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SumCp».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_SumCp_hypotheses_inhabited_4ffa720a0d9f
