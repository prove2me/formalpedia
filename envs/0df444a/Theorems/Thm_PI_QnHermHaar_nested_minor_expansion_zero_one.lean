-- Prove2me | Theorems.Thm_PI_QnHermHaar_nested_minor_expansion_zero_one
-- name    : PI.QnHermHaar.nested_minor_expansion_zero_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:00:29.834575+00:00
-- url     : https://prove2.me/theorems/77fbdd1d-c1a7-4316-a8ca-1344971e967a
-- title:
--   Qn Herm Haar: nested minor expansion zero one
-- statement:
--   The Qn Herm Haar construction uses the nested minor expansion zero one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L136-L140

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

theorem PI.QnHermHaar.nested_minor_expansion_zero_one {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin (t + 1) → Fin (t + 1) → A)
    (Y Yb : Fin (t + 1) → A) (x xb : Fin (t + 1) → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 0 1 = -∑ i : Fin (t + 1), ∑ j : Fin (t + 1),
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (Yb i * qminor E i.succAbove j.succAbove (u - 1)) := by sorry
