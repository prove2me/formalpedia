-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_range_8f1b7a26fca2
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_range_8f1b7a26fca2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:34.658125+00:00
-- url     : https://prove2.me/theorems/5b0e0ba7-fe11-504f-973a-721e595d4b6c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum choose range 8f1b7a26fca2: P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum choose range 8f1b7a26fca2
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum choose range 8f1b7a26fca2 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum choose range 8f1b7a26fca2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGridSum.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGridSum.lean#L30-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGridSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Finset Filter Asymptotics

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_range_8f1b7a26fca2 (n i j : ℕ) :
    ∑ a ∈ range n, a.choose i * (n - 1 - a).choose j = n.choose (i + j + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GridSum».«choose_range» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_range_8f1b7a26fca2
