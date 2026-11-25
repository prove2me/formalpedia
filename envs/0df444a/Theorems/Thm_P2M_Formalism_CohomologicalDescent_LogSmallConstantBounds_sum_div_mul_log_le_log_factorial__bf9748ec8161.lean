-- Prove2me | Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_div_mul_log_le_log_factorial__bf9748ec8161
-- name    : P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_div_mul_log_le_log_factorial__bf9748ec8161
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:02.723075+00:00
-- url     : https://prove2.me/theorems/a9e4f5cf-779c-493d-90eb-221395cf7665
-- title:
--   P2 M Formalism Cohomological Descent Log Small Constant Bounds sum div mul log le log factorial  bf9748ec8161: P2 M Formalism Cohomological Descent Log Small Constant Bounds sum div mul log le log fac
-- statement:
--   The P2 M Formalism Cohomological Descent Log Small Constant Bounds sum div mul log le log factorial  bf9748ec8161 construction uses the P2 M Formalism Cohomological Descent Log Small Constant Bounds sum div mul log le log factorial  bf9748ec8161 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L1120-L1158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L1120-L1158

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical

theorem P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_div_mul_log_le_log_factorial__bf9748ec8161 (n : ℕ) :
    ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) ≤
      Real.log ((n.factorial : ℕ) : ℝ) := by sorry

alias «Formalism».«CohomologicalDescent».«LogSmallConstantBounds».«sum_div_mul_log_le_log_factorial'» := P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_div_mul_log_le_log_factorial__bf9748ec8161
