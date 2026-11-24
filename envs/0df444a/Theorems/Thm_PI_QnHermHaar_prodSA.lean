-- Prove2me | Theorems.Thm_PI_QnHermHaar_prodSA
-- name    : PI.QnHermHaar.prodSA
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:40:21.832503+00:00
-- url     : https://prove2.me/theorems/fa47a745-532e-45a8-bf57-9532449003f8
-- title:
--   Qn Herm Haar: prod SA
-- statement:
--   The Qn Herm Haar construction uses the prod SA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L94-L96

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

theorem PI.QnHermHaar.prodSA {t : ℕ} (ε : Fin (t + 1) → ℤˣ) (i : Fin (t + 1)) :
    ∏ k, ε (i.succAbove k) = ε i * ∏ k, ε k := by sorry
