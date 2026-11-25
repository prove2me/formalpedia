-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isMultiHomog_X_line_5b92169b8b7f
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isMultiHomog_X_line_5b92169b8b7f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:37:27.430807+00:00
-- url     : https://prove2.me/theorems/13e9fcfb-994a-50f1-83c5-1fdce67132ca
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line is Multi Homog X line 5b92169b8b7f: P2 M Ground Theory Heights  Heights Lower Bound Free Line is Multi Homog X line 5b92169b8b7f
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line is Multi Homog X line 5b92169b8b7f construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line is Multi Homog X line 5b92169b8b7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/LineField.lean#L130-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/LineField.lean#L130-L136

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isMultiHomog_X_line_5b92169b8b7f (i : Fin 2) :
    IsMultiHomog (X ⟨(), i⟩ : MRing (PBlk 2)) (fun _ => 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«isMultiHomog_X_line» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isMultiHomog_X_line_5b92169b8b7f
