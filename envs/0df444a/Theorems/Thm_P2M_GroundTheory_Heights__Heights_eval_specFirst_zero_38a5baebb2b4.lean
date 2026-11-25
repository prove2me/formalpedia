-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_specFirst_zero_38a5baebb2b4
-- name    : P2M_GroundTheory_Heights__Heights_eval_specFirst_zero_38a5baebb2b4
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:16.339806+00:00
-- url     : https://prove2.me/theorems/86682e34-dc91-4f6f-bfd6-4c47254a0c97
-- title:
--   P2 M Ground Theory Heights  Heights eval spec First zero 38a5baebb2b4: P2 M Ground Theory Heights  Heights eval spec First zero 38a5baebb2b4
-- statement:
--   The P2 M Ground Theory Heights  Heights eval spec First zero 38a5baebb2b4 construction uses the P2 M Ground Theory Heights  Heights eval spec First zero 38a5baebb2b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PMahlerZeroSpec.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PMahlerZeroSpec.lean#L9-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PMahlerZeroSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open MeasureTheory MvPolynomial
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights

theorem P2M_GroundTheory_Heights__Heights_eval_specFirst_zero_38a5baebb2b4 {n : ℕ} (f : MvPolynomial (Fin 1 × Fin n) ℂ) (u : Fin n → ℂ)
    (v : Fin 0 × Fin n → ℂ) : eval v (specFirst f u) = eval (fun ij => u ij.2) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_specFirst_zero» := P2M_GroundTheory_Heights__Heights_eval_specFirst_zero_38a5baebb2b4
