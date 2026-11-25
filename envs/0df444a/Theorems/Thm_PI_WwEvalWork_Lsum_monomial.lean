-- Prove2me | Theorems.Thm_PI_WwEvalWork_Lsum_monomial
-- name    : PI.WwEvalWork.Lsum_monomial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:25.779006+00:00
-- url     : https://prove2.me/theorems/ad165dcc-d6a6-5ccf-a16d-fbe39d5bc5f0
-- title:
--   Ww Eval Work: Lsum monomial
-- statement:
--   The Ww Eval Work construction uses the Lsum monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L44-L48

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
variable {σ K : Type*} [CommRing K]

theorem PI.WwEvalWork.Lsum_monomial (w : (σ →₀ ℕ) → K) (α : σ →₀ ℕ) (r : K) :
    Lsum w (monomial α r) = r * w α := by sorry
