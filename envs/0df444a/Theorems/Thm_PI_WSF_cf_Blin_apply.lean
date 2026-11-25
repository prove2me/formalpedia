-- Prove2me | Theorems.Thm_PI_WSF_cf_Blin_apply
-- name    : PI.WSF.cf_Blin_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:38.608658+00:00
-- url     : https://prove2.me/theorems/10485e9c-5467-598e-b0bc-1696cdd9faa8
-- title:
--   WSF: cf Blin apply
-- statement:
--   The WSF construction uses the cf Blin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CfEqSumOfSubset.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CfEqSumOfSubset.lean#L57-L58

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CfEqSumOfSubset
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
open Formalism.BasicNotions MvPolynomial

theorem PI.WSF.cf_Blin_apply {N : ℕ} (lam : DomWeight N) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Blin lam q p = normFock lam p q := by sorry
