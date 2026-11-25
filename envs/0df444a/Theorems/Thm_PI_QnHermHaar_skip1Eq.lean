-- Prove2me | Theorems.Thm_PI_QnHermHaar_skip1Eq
-- name    : PI.QnHermHaar.skip1Eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:00:42.019147+00:00
-- url     : https://prove2.me/theorems/714ffb8e-c45a-4d45-8031-4c7f3fe2e6c5
-- title:
--   Qn Herm Haar: skip1 Eq
-- statement:
--   The Qn Herm Haar construction uses the skip1 Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L16-L20

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

theorem PI.QnHermHaar.skip1Eq {t : ℕ} (i : Fin (t + 1)) (j : Fin t) : skip1 i j = i.succAbove j := by sorry
