-- Prove2me | Theorems.Thm_PI_WSF_evA_fock_right
-- name    : PI.WSF.evA_fock_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:34.356805+00:00
-- url     : https://prove2.me/theorems/90ece186-cee1-50ce-8b02-b856cf56fa6f
-- title:
--   WSF: ev A fock right
-- statement:
--   The WSF construction uses the ev A fock right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/ConstructionA.lean#L76-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/ConstructionA.lean#L76-L88

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

theorem PI.WSF.evA_fock_right {σ : Type*} (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f g = ∑ m ∈ g.support,
      f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by sorry
