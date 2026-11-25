-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_smooth_adjoin_of_transcendental_1b0cb7f0067d
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_smooth_adjoin_of_transcendental_1b0cb7f0067d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:28:36.089815+00:00
-- url     : https://prove2.me/theorems/f18af830-98a1-4b64-a326-f4fa66aab158
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line smooth adjoin of transcendental 1b0cb7f0067d: P2 M Ground Theory Heights  Heights Lower Bound Free Line smooth adjoin of transcendental 1b0cb7
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line smooth adjoin of transcendental 1b0cb7f0067d construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line smooth adjoin of transcendental 1b0cb7f0067d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/LineField.lean#L184-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/LineField.lean#L184-L191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_smooth_adjoin_of_transcendental_1b0cb7f0067d {A : Type} [Field A] [Algebra ℚ A] {v : A}
    (hv : Transcendental ℚ v) (s : Set A) (hs : Algebra.adjoin ℚ s = Algebra.adjoin ℚ {v}) :
    Algebra.Smooth ℚ (Algebra.adjoin ℚ s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«smooth_adjoin_of_transcendental» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_smooth_adjoin_of_transcendental_1b0cb7f0067d
