-- Prove2me | Theorems.Thm_PI_QnHermHaar_pairSum
-- name    : PI.QnHermHaar.pairSum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:36:45.726809+00:00
-- url     : https://prove2.me/theorems/7b0c2124-7a8f-59ac-96a9-fb6461ec81b6
-- title:
--   Qn Herm Haar: pair Sum
-- statement:
--   The Qn Herm Haar construction uses the pair Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L47-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L47-L84

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

theorem PI.QnHermHaar.pairSum {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (c d : Fin (t + 2) → A)
    (G : (Fin t → Fin (t + 2)) → A) :
    ∑ i : Fin (t + 2), ∑ i' : Fin (t + 2),
        (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • ((c i * d i' - c i' * d i) * G (skip2 i i')) else 0) =
      ∑ i' : Fin (t + 2), ∑ k : Fin (t + 1),
        ((-1 : ℂ) ^ ((i' : ℕ) + (k : ℕ))) • (c (i'.succAbove k) * d i' * G (i'.succAbove ∘ k.succAbove)) := by sorry
