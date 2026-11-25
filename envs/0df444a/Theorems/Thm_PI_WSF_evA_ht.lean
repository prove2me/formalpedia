-- Prove2me | Theorems.Thm_PI_WSF_evA_ht
-- name    : PI.WSF.evA_ht
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:47:41.987483+00:00
-- url     : https://prove2.me/theorems/8a81ca2c-a19d-5e40-a21f-c016e30eab97
-- title:
--   WSF: ev A ht
-- statement:
--   The WSF construction uses the ev A ht property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/ConstructionA.lean#L64-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/ConstructionA.lean#L64-L74

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_ConstructionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial MeasureTheory

theorem PI.WSF.evA_ht {N : ℕ} (μ ν : Fin N → ℕ)
    (h1 : ∀ k : ℕ, (∑ a : Fin N with a.val < k, μ a) ≤ ∑ a : Fin N with a.val < k, ν a)
    (h2 : ∑ a : Fin N, μ a = ∑ a : Fin N, ν a) :
    ∑ a : Fin N, (a.val : ℤ) * (ν a : ℤ) ≤ ∑ a : Fin N, (a.val : ℤ) * (μ a : ℤ) := by sorry
