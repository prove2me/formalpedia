-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_weberValue_of_a__eq_zero_6d58591c3e51
-- name    : P2M_GroundTheory_Global_weberValue_of_a__eq_zero_6d58591c3e51
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:54.897824+00:00
-- url     : https://prove2.me/theorems/d9240668-675a-490c-86ab-dcc591367e55
-- title:
--   P2 M Ground Theory Global weber Value of a  eq zero 6d58591c3e51: P2 M Ground Theory Global weber Value of a  eq zero 6d58591c3e51
-- statement:
--   The P2 M Ground Theory Global weber Value of a  eq zero 6d58591c3e51 construction uses the P2 M Ground Theory Global weber Value of a  eq zero 6d58591c3e51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L66-L68

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

theorem P2M_GroundTheory_Global_weberValue_of_a__eq_zero_6d58591c3e51 {W : WeierstrassCurve F} (ha : W.a₄ = 0) (hb : W.a₆ ≠ 0)
    (x : F) : weberValue W x = g₃ W / W.Δ * x ^ 3 := by sorry

alias «GroundTheory».«Global».«weberValue_of_a₄_eq_zero» := P2M_GroundTheory_Global_weberValue_of_a__eq_zero_6d58591c3e51
