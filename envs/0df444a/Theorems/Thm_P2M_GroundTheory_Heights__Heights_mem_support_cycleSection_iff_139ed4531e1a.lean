-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_support_cycleSection_iff_139ed4531e1a
-- name    : P2M_GroundTheory_Heights__Heights_mem_support_cycleSection_iff_139ed4531e1a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:49:43.495728+00:00
-- url     : https://prove2.me/theorems/81a9a567-7f92-4d08-9600-307656e0c0fc
-- title:
--   P2 M Ground Theory Heights  Heights mem support cycle Section iff 139ed4531e1a: P2 M Ground Theory Heights  Heights mem support cycle Section iff 139ed4531e1a
-- statement:
--   The P2 M Ground Theory Heights  Heights mem support cycle Section iff 139ed4531e1a construction uses the P2 M Ground Theory Heights  Heights mem support cycle Section iff 139ed4531e1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSupportCycleSection.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSupportCycleSection.lean#L7-L12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSupportCycleSection
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

theorem P2M_GroundTheory_Heights__Heights_mem_support_cycleSection_iff_139ed4531e1a {n : ℕ} (Z : ProjCycle ℂ n) (u : Fin n → ℂ)
    (W' : Ideal (MvPolynomial (Fin n) ℂ)) :
    W' ∈ (cycleSection Z u).support ↔ ∃ W ∈ Z.support, W' ∈ (divCycle W u).support := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_support_cycleSection_iff» := P2M_GroundTheory_Heights__Heights_mem_support_cycleSection_iff_139ed4531e1a
