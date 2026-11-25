-- Prove2me | Theorems.Thm_PI_FrameInd_NegB_eq_zero_of_negMap
-- name    : PI.FrameInd.NegB.eq_zero_of_negMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:55.098407+00:00
-- url     : https://prove2.me/theorems/e9346e4b-7fd5-49c0-a21b-1781a0350f50
-- title:
--   Neg B: eq zero of neg Map
-- statement:
--   The Neg B construction uses the eq zero of neg Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/EqZeroOfNegMap.lean#L35-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/EqZeroOfNegMap.lean#L35-L64

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_EqZeroOfNegMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.FrameInd PI.FrameInd.NegB

theorem PI.FrameInd.NegB.eq_zero_of_negMap (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (hx : negMap k r x = 0)
    (hre : (herm (Hpk k r) x x).re ≤ 0) : x = 0 := by sorry
