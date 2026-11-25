-- Prove2me | Theorems.Thm_PI_WSF_evA_dom
-- name    : PI.WSF.evA_dom
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:42.016559+00:00
-- url     : https://prove2.me/theorems/7d20afc6-6ec6-5661-8d40-061a52205332
-- title:
--   WSF: ev A dom
-- statement:
--   The WSF construction uses the ev A dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/ConstructionA.lean#L21-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/ConstructionA.lean#L21-L44

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

theorem PI.WSF.evA_dom {N : ℕ} (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin N with a.val < k, Formalism.GradedWeylDivisibility.rowDeg m a) ≤ ∑ t : Fin N with t.val < k, ν t) ∧
      ∑ a : Fin N, Formalism.GradedWeylDivisibility.rowDeg m a = ∑ t : Fin N, ν t := by sorry
