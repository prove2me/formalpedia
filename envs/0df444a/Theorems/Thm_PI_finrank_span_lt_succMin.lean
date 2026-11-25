-- Prove2me | Theorems.Thm_PI_finrank_span_lt_succMin
-- name    : PI.finrank_span_lt_succMin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:46:53.306296+00:00
-- url     : https://prove2.me/theorems/591d8178-2be0-4865-b378-a243f72b0e62
-- title:
--   PI: finrank span lt succ Min
-- statement:
--   The PI construction uses the finrank span lt succ Min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/Minima.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/Minima.lean#L14-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Minima
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped InnerProductSpace
open PI
variable {N : ℕ}

theorem PI.finrank_span_lt_succMin (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (i : ℕ) (hi : 1 ≤ i) :
    finrank ℝ (Submodule.span ℝ {x : EuclideanSpace ℝ (Fin N) | x ∈ M ∧ ‖x‖ < succMin M i}) < i := by sorry
