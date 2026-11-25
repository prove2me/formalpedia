-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechTop_idx_isEmpty_10e419feb8ed
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechTop_idx_isEmpty_10e419feb8ed
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:16.455798+00:00
-- url     : https://prove2.me/theorems/88a73946-c2cf-5863-b6d4-1ae773402490
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Top idx is Empty 10e419feb8ed: P2 M Ground Theory Heights  Heights Kleiman Cech Top idx is Empty 10e419feb8ed
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Top idx is Empty 10e419feb8ed construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Top idx is Empty 10e419feb8ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechTop.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechTop.lean#L7-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechTop_idx_isEmpty_10e419feb8ed (N i : ℕ) (hi : N < i) :
    IsEmpty (Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechTop».«idx_isEmpty» := P2M_GroundTheory_Heights__Heights_Kleiman_CechTop_idx_isEmpty_10e419feb8ed
