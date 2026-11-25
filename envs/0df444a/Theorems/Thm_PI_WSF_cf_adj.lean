-- Prove2me | Theorems.Thm_PI_WSF_cf_adj
-- name    : PI.WSF.cf_adj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:41.538472+00:00
-- url     : https://prove2.me/theorems/ad3b4658-5c32-4587-a7c1-ca4632d2931a
-- title:
--   WSF: cf adj
-- statement:
--   The WSF construction uses the cf adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CfEqSumOfSubset.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CfEqSumOfSubset.lean#L79-L83

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

theorem PI.WSF.cf_adj {N : ℕ} (lam : DomWeight N) (g : Matrix (Fin N) (Fin N) ℂ)
    (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (Formalism.GradedWeylDivisibility.rowAct ℂ g p) q = normFock lam p (Formalism.GradedWeylDivisibility.rowAct ℂ g.conjTranspose q) := by sorry
