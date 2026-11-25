-- Prove2me | Theorems.Thm_PI_WwEvalWork_peval_monomial
-- name    : PI.WwEvalWork.peval_monomial
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:53.058117+00:00
-- url     : https://prove2.me/theorems/3c217a54-6e8c-5282-bc7a-8629e9d70d47
-- title:
--   Ww Eval Work: peval monomial
-- statement:
--   The Ww Eval Work construction uses the peval monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L59-L70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwEvalWork
open MvPolynomial
variable {σ1 σ2 K : Type*} [CommRing K]

theorem PI.WwEvalWork.peval_monomial (x : σ1 → K) (μ : σ1 ⊕ σ2 →₀ ℕ) (c : ℤ) :
    peval x (monomial μ c) = monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).2
      ((c : K) * (Finsupp.sumFinsuppEquivProdFinsupp μ).1.prod fun v e => x v ^ e) := by sorry
