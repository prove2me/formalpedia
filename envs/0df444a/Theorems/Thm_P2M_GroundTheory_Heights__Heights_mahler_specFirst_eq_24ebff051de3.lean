-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mahler_specFirst_eq_24ebff051de3
-- name    : P2M_GroundTheory_Heights__Heights_mahler_specFirst_eq_24ebff051de3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:43.401687+00:00
-- url     : https://prove2.me/theorems/215532d9-45db-48f3-87d2-71faba49e05e
-- title:
--   P2 M Ground Theory Heights  Heights mahler spec First eq 24ebff051de3: P2 M Ground Theory Heights  Heights mahler spec First eq 24ebff051de3
-- statement:
--   The P2 M Ground Theory Heights  Heights mahler spec First eq 24ebff051de3 construction uses the P2 M Ground Theory Heights  Heights mahler spec First eq 24ebff051de3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PMahlerAverageSplit.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PMahlerAverageSplit.lean#L11-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PMahlerAverageSplit
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
open MvPolynomial MeasureTheory
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_mahler_specFirst_eq_24ebff051de3 (h3 : EvalSpecFirst.Statement) {n e : ℕ} (h : HermNorm n)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (v : Fin n → ℂ) :
    mahler h e (specFirst f v) =
      sphereMean h e (fun w => Real.log ‖eval (consGroup v w) f‖) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mahler_specFirst_eq» := P2M_GroundTheory_Heights__Heights_mahler_specFirst_eq_24ebff051de3
