-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_weberValue_of_a__eq_zero_1cba6dac3294
-- name    : P2M_GroundTheory_Global_weberValue_of_a__eq_zero_1cba6dac3294
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:53.736241+00:00
-- url     : https://prove2.me/theorems/c2f1b717-df83-48a6-94a3-32dd39128063
-- title:
--   P2 M Ground Theory Global weber Value of a  eq zero 1cba6dac3294: P2 M Ground Theory Global weber Value of a  eq zero 1cba6dac3294
-- statement:
--   The P2 M Ground Theory Global weber Value of a  eq zero 1cba6dac3294 construction uses the P2 M Ground Theory Global weber Value of a  eq zero 1cba6dac3294 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L62-L64

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

theorem P2M_GroundTheory_Global_weberValue_of_a__eq_zero_1cba6dac3294 {W : WeierstrassCurve F} (hb : W.a₆ = 0) (x : F) :
    weberValue W x = g₂ W ^ 2 / W.Δ * x ^ 2 := by sorry

alias «GroundTheory».«Global».«weberValue_of_a₆_eq_zero» := P2M_GroundTheory_Global_weberValue_of_a__eq_zero_1cba6dac3294
