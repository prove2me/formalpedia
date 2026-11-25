-- Prove2me | Theorems.Thm_PI_QnWCellW_prod_eq_Wm
-- name    : PI.QnWCellW.prod_eq_Wm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:28:06.332657+00:00
-- url     : https://prove2.me/theorems/6eb8c01b-3c0d-429c-bc3b-42db9f058ae5
-- title:
--   Qn WCell W: prod eq Wm
-- statement:
--   The Qn WCell W construction uses the prod eq Wm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L111-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L111-L123

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

theorem PI.QnWCellW.prod_eq_Wm (k r : ℕ) (c : Fin r → ℂ) : ∀ L : List (Fin r), L.Nodup →
    (L.map fun a => w1 k r a (c a)).prod = Wm k r (L.map Fin.val).toFinset c
  := by sorry
