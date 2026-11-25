-- Prove2me | Theorems.Thm_PI_FrameInd_NegB_herm_Pk
-- name    : PI.FrameInd.NegB.herm_Pk
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:31:01.572466+00:00
-- url     : https://prove2.me/theorems/a592c994-286b-426c-9c13-7a98f0bcbdf3
-- title:
--   Neg B: herm Pk
-- statement:
--   The Neg B construction uses the herm Pk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/EqZeroOfNegMap.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/EqZeroOfNegMap.lean#L8-L13

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

theorem PI.FrameInd.NegB.herm_Pk (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x x = ∑ i, star ((Pk k r *ᵥ x) i) * (dK k r i * (Pk k r *ᵥ x) i) := by sorry
