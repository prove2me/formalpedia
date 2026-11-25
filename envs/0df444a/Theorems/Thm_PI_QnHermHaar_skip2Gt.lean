-- Prove2me | Theorems.Thm_PI_QnHermHaar_skip2Gt
-- name    : PI.QnHermHaar.skip2Gt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:18.617093+00:00
-- url     : https://prove2.me/theorems/698d5baf-c1e8-4e50-9688-74951d8e4f18
-- title:
--   Qn Herm Haar: skip2 Gt
-- statement:
--   The Qn Herm Haar construction uses the skip2 Gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L39-L45

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

theorem PI.QnHermHaar.skip2Gt {t : ℕ} (i' : Fin (t + 2)) (k : Fin (t + 1)) (h : ¬ (k : ℕ) < (i' : ℕ)) :
    (skip2 i' (i'.succAbove k) : Fin t → Fin (t + 2)) = i'.succAbove ∘ k.succAbove := by sorry
