-- Prove2me | Theorems.Thm_PI_WwEvalWork_Lsum_finset_sum
-- name    : PI.WwEvalWork.Lsum_finset_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:31.67774+00:00
-- url     : https://prove2.me/theorems/d3293522-8496-4b97-95dd-4832255be2af
-- title:
--   Ww Eval Work: Lsum finset sum
-- statement:
--   The Ww Eval Work construction uses the Lsum finset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L37-L42

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

theorem PI.WwEvalWork.Lsum_finset_sum {ι : Type*} (w : (σ →₀ ℕ) → K) (s : Finset ι)
    (f : ι → MvPolynomial σ K) : Lsum w (∑ i ∈ s, f i) = ∑ i ∈ s, Lsum w (f i) := by sorry
