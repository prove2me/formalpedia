-- Prove2me | Theorems.Thm_PI_StabBigW_sum_mid
-- name    : PI.StabBigW.sum_mid
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:35.986519+00:00
-- url     : https://prove2.me/theorems/9ff4a077-e9f6-4828-8c0c-2c992c203ab2
-- title:
--   Stab Big W: sum mid
-- statement:
--   The Stab Big W construction uses the sum mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L279-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L279-L296

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}

theorem PI.StabBigW.sum_mid (f : Fin (2 * r + k + 1) → ℂ)
    (hf : ∀ m : Fin (2 * r + k + 1), (m.val < r ∨ r + k < m.val) → f m = 0) :
    ∑ m, f m = ∑ s : Fin (k + 1), f (wI k r s) := by sorry
