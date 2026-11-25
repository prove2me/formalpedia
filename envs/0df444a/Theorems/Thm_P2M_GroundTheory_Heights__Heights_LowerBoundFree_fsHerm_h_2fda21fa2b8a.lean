-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_fsHerm_h_2fda21fa2b8a
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_fsHerm_h_2fda21fa2b8a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:19.473728+00:00
-- url     : https://prove2.me/theorems/526c3dcd-9df1-59e7-9824-52f23542b318
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free fs Herm h 2fda21fa2b8a: P2 M Ground Theory Heights  Heights Lower Bound Free fs Herm h 2fda21fa2b8a
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free fs Herm h 2fda21fa2b8a construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free fs Herm h 2fda21fa2b8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FlagIndices/InstFintypeFlIdx.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FlagIndices/InstFintypeFlIdx.lean#L24-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_HasCoverByOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FlagIndices_InstFintypeFlIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_fsHerm_h_2fda21fa2b8a (a : K → ℤ) (z : (Σ k, ι k) → ℂ) : (fsHerm ι a).h z = refNorm a z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«fsHerm_h» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_fsHerm_h_2fda21fa2b8a
