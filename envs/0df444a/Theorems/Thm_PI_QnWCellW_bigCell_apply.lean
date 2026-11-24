-- Prove2me | Theorems.Thm_PI_QnWCellW_bigCell_apply
-- name    : PI.QnWCellW.bigCell_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:44:56.74181+00:00
-- url     : https://prove2.me/theorems/b9f9d489-c17d-48fb-9070-578bf178efaf
-- title:
--   Qn WCell W: big Cell apply
-- statement:
--   The Qn WCell W construction uses the big Cell apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L176-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L176-L202

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

theorem PI.QnWCellW.bigCell_apply (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (p q : Fin (2 * r + k + 1)) :
    bigCell k r c μ p q =
      if q.val < r then (if p.val = 2 * r + k - q.val then cN r c q.val else 0)
      else if q.val ≤ r + k then
        (if r ≤ p.val ∧ p.val ≤ r + k then μE μ (p.val - r) (q.val - r) else 0)
      else (if p.val = 2 * r + k - q.val then (star (cN r c (2 * r + k - q.val)))⁻¹ else 0) := by sorry
