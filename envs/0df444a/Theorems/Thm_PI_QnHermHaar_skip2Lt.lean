-- Prove2me | Theorems.Thm_PI_QnHermHaar_skip2Lt
-- name    : PI.QnHermHaar.skip2Lt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:12:35.645798+00:00
-- url     : https://prove2.me/theorems/bed1abb8-ac86-4992-a971-657ef61f7724
-- title:
--   Qn Herm Haar: skip2 Lt
-- statement:
--   The Qn Herm Haar construction uses the skip2 Lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L31-L37

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

theorem PI.QnHermHaar.skip2Lt {t : ℕ} (i' : Fin (t + 2)) (k : Fin (t + 1)) (h : (k : ℕ) < (i' : ℕ)) :
    (skip2 (i'.succAbove k) i' : Fin t → Fin (t + 2)) = i'.succAbove ∘ k.succAbove := by sorry
