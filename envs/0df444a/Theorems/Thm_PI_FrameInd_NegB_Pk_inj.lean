-- Prove2me | Theorems.Thm_PI_FrameInd_NegB_Pk_inj
-- name    : PI.FrameInd.NegB.Pk_inj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:44.454943+00:00
-- url     : https://prove2.me/theorems/d71e9648-a2ca-4e01-9495-1498ce76c0cf
-- title:
--   Neg B: Pk inj
-- statement:
--   The Neg B construction uses the Pk inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/EqZeroOfNegMap.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/EqZeroOfNegMap.lean#L23-L29

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

theorem PI.FrameInd.NegB.Pk_inj (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (h : Pk k r *ᵥ x = 0) : x = 0 := by sorry
