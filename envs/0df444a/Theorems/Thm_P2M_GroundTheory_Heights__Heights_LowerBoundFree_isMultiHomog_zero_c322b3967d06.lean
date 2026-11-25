-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_zero_c322b3967d06
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_zero_c322b3967d06
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:27:49.100374+00:00
-- url     : https://prove2.me/theorems/21c17ebd-bb5f-4905-aece-a8bb3634c821
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog zero c322b3967d06: P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog zero c322b3967d06
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog zero c322b3967d06 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog zero c322b3967d06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
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
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_zero_c322b3967d06 (d : K → ℕ) : IsMultiHomog (0 : MRing ι) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isMultiHomog_zero» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_zero_c322b3967d06
