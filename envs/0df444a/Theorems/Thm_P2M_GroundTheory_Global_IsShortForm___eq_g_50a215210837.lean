-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_IsShortForm___eq_g_50a215210837
-- name    : P2M_GroundTheory_Global_IsShortForm___eq_g_50a215210837
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:08:04.985859+00:00
-- url     : https://prove2.me/theorems/7f2e79f7-7b7d-4f61-a29b-5ffa950f3ff2
-- title:
--   P2 M Ground Theory Global Is Short Form   eq g 50a215210837: P2 M Ground Theory Global Is Short Form   eq g 50a215210837
-- statement:
--   The P2 M Ground Theory Global Is Short Form   eq g 50a215210837 construction uses the P2 M Ground Theory Global Is Short Form   eq g 50a215210837 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L31-L34

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint
variable {F : Type*} [Field F]
open ShortWeierstrass

theorem P2M_GroundTheory_Global_IsShortForm___eq_g_50a215210837 {W : WeierstrassCurve F} (hW : IsShortForm W) :
    W.Δ = g₂ W ^ 3 - 27 * g₃ W ^ 2 := by sorry

alias «GroundTheory».«Global».«IsShortForm».«Δ_eq_g» := P2M_GroundTheory_Global_IsShortForm___eq_g_50a215210837
