-- Prove2me | Theorems.Thm_PI_QnHermHaar_valSuccAbove
-- name    : PI.QnHermHaar.valSuccAbove
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:16:23.492075+00:00
-- url     : https://prove2.me/theorems/15504811-6d93-4247-acbd-cfa4bdf1f161
-- title:
--   Qn Herm Haar: val Succ Above
-- statement:
--   The Qn Herm Haar construction uses the val Succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L11-L14

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnHermHaar.valSuccAbove {n : ℕ} (p : Fin (n + 1)) (x : Fin n) :
    (p.succAbove x).val = if x.val < p.val then x.val else x.val + 1 := by sorry
