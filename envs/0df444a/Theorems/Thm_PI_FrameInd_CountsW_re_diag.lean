-- Prove2me | Theorems.Thm_PI_FrameInd_CountsW_re_diag
-- name    : PI.FrameInd.CountsW.re_diag
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:54:43.242798+00:00
-- url     : https://prove2.me/theorems/0fec7b91-2590-446d-ac00-f855ed9c1102
-- title:
--   Counts W: re diag
-- statement:
--   The Counts W construction uses the re diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/Counts.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/Counts.lean#L41-L48

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

theorem PI.FrameInd.CountsW.re_diag {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (w : n → ℂ) :
    (herm A ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w) ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w)).re =
      ∑ i, hA.eigenvalues i * Complex.normSq (w i) := by sorry
