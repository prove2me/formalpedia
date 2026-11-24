-- Prove2me | Theorems.Thm_PI_QnWCellW_main
-- name    : PI.QnWCellW.main
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:45:11.342281+00:00
-- url     : https://prove2.me/theorems/193ed095-1f58-42d9-8508-3dd098f19fb3
-- title:
--   Qn WCell W: main
-- statement:
--   The Qn WCell W construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L209-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L209-L218

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnWCellW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
set_option maxHeartbeats 1000000

theorem PI.QnWCellW.main (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    bigCell k r c μ =
      wCell k r (Fin.last r) c * bigCell k r (fun _ => 1) μ * wCell k r (Fin.last r) (fun _ => 1) := by sorry
