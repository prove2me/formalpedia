-- Prove2me | Theorems.Thm_PI_FrameInd_CountsW_diag_eq
-- name    : PI.FrameInd.CountsW.diag_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:53:45.649239+00:00
-- url     : https://prove2.me/theorems/117e10b1-1d80-4dbb-bb2b-a0bcfeff708f
-- title:
--   Counts W: diag eq
-- statement:
--   The Counts W construction uses the diag eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/Counts.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/Counts.lean#L24-L29

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

theorem PI.FrameInd.CountsW.diag_eq {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * A * (hA.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) := by sorry
