-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_div_le_padicValNat_factorial_9a940f801ab9
-- name    : P2M_GroundTheory_Heights__Heights_Model_div_le_padicValNat_factorial_9a940f801ab9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:23.762869+00:00
-- url     : https://prove2.me/theorems/b7858179-0ef7-4e6f-bd1f-25dc8651b92c
-- title:
--   P2 M Ground Theory Heights  Heights Model div le padic Val Nat factorial 9a940f801ab9: P2 M Ground Theory Heights  Heights Model div le padic Val Nat factorial 9a940f801ab9
-- statement:
--   The P2 M Ground Theory Heights  Heights Model div le padic Val Nat factorial 9a940f801ab9 construction uses the P2 M Ground Theory Heights  Heights Model div le padic Val Nat factorial 9a940f801ab9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PMertensUpper.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PMertensUpper.lean#L9-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PMertensUpper
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
open Real

theorem P2M_GroundTheory_Heights__Heights_Model_div_le_padicValNat_factorial_9a940f801ab9 (N p : ℕ) (hp : p.Prime) :
    N / p ≤ padicValNat p N.factorial := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«div_le_padicValNat_factorial» := P2M_GroundTheory_Heights__Heights_Model_div_le_padicValNat_factorial_9a940f801ab9
