-- Prove2me | Theorems.Thm_PI_FrameInd_CountsW_U_eq_zero
-- name    : PI.FrameInd.CountsW.U_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:01:57.6377+00:00
-- url     : https://prove2.me/theorems/b8c0dd19-4f4d-5d38-b92c-47aa793a838a
-- title:
--   Counts W: U eq zero
-- statement:
--   The Counts W construction uses the U eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/Counts.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/Counts.lean#L31-L39

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NonposCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd PI.FrameInd.CountsW
open PI.FrameInd

theorem PI.FrameInd.CountsW.U_eq_zero {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (w : n → ℂ) (hw : (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w = 0) : w = 0 := by sorry
