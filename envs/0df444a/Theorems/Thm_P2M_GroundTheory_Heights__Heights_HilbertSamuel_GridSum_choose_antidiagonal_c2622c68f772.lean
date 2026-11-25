-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_antidiagonal_c2622c68f772
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_antidiagonal_c2622c68f772
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:42.211262+00:00
-- url     : https://prove2.me/theorems/44e48ed7-4010-5f57-ba38-8a7440b5cf7c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum choose antidiagonal c2622c68f772: P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum choose antidiagonal c2622c68f772
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum choose antidiagonal c2622c68f772 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Grid Sum choose antidiagonal c2622c68f772 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGridSum.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGridSum.lean#L9-L28

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_antidiagonal_c2622c68f772 (m i j : ℕ) :
    ∑ p ∈ antidiagonal m, p.1.choose i * p.2.choose j = (m + 1).choose (i + j + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GridSum».«choose_antidiagonal» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_antidiagonal_c2622c68f772
