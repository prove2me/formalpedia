-- Prove2me | Theorems.Thm_PI_QnWCellW_weyl_cell_mul_apply
-- name    : PI.QnWCellW.weyl_cell_mul_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:48:59.975188+00:00
-- url     : https://prove2.me/theorems/87103edc-a543-44b6-9af1-dfd3bf667963
-- title:
--   Qn WCell W: weyl cell mul apply
-- statement:
--   The Qn WCell W construction uses the weyl cell mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L58-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L58-L82

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

theorem PI.QnWCellW.weyl_cell_mul_apply (k r : ℕ) (l : Fin r) (d : ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (w1 k r l d * M) p q =
      if p = esI k r l then d * M (eI k r l) q
      else if p = eI k r l then (star d)⁻¹ * M (esI k r l) q else M p q := by sorry
