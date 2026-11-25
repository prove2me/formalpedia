-- Prove2me | Theorems.Thm_PI_WwEvalWork_Lsum_add
-- name    : PI.WwEvalWork.Lsum_add
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:30.606019+00:00
-- url     : https://prove2.me/theorems/978e6ba5-eb32-42d6-ba0b-17e122575242
-- title:
--   Ww Eval Work: Lsum add
-- statement:
--   The Ww Eval Work construction uses the Lsum add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L24-L32

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

theorem PI.WwEvalWork.Lsum_add (w : (σ →₀ ℕ) → K) (p q : MvPolynomial σ K) :
    Lsum w (p + q) = Lsum w p + Lsum w q := by sorry
