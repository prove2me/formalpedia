-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_anchor_homog_32008f5c06f9
-- name    : P2M_GroundTheory_Heights__Heights_anchor_homog_32008f5c06f9
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:13.088425+00:00
-- url     : https://prove2.me/theorems/f12f85b8-0461-49b4-84e1-c79445d864f0
-- title:
--   P2 M Ground Theory Heights  Heights anchor homog 32008f5c06f9: P2 M Ground Theory Heights  Heights anchor homog 32008f5c06f9
-- statement:
--   The P2 M Ground Theory Heights  Heights anchor homog 32008f5c06f9 construction uses the P2 M Ground Theory Heights  Heights anchor homog 32008f5c06f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootHeightNE.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootHeightNE.lean#L11-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootHeightNE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_anchor_homog_32008f5c06f9 (f j m : ℕ) : IsMultiHomog (rootAnchorSection f j m) (fun _ => 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«anchor_homog» := P2M_GroundTheory_Heights__Heights_anchor_homog_32008f5c06f9
