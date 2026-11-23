-- Prove2me | Theorems.Thm_PI_WwEvalWork_Lsum_eq_of_subset
-- name    : PI.WwEvalWork.Lsum_eq_of_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:20.818571+00:00
-- url     : https://prove2.me/theorems/64de1128-162a-49bf-8af6-67ccc1be7808
-- title:
--   Ww Eval Work: Lsum eq of subset
-- statement:
--   The Ww Eval Work construction uses the Lsum eq of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L17-L22

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

theorem PI.WwEvalWork.Lsum_eq_of_subset (w : (σ →₀ ℕ) → K) (Q : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (h : Q.support ⊆ S) : Lsum w Q = ∑ α ∈ S, coeff α Q * w α := by sorry
