-- Prove2me | Theorems.Thm_PI_FrameInd_herm_Vc
-- name    : PI.FrameInd.herm_Vc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:38:59.5403+00:00
-- url     : https://prove2.me/theorems/6af4479d-7a85-46b4-b42b-79d6579e4bd0
-- title:
--   Frame Ind: herm Vc
-- statement:
--   The Frame Ind construction uses the herm Vc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L34-L36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet
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
open PI PI.FrameInd

theorem PI.FrameInd.herm_Vc (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (c d : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) (Vc k r z z' g *ᵥ c) (Vc k r z z' g *ᵥ d) = herm (gramM k r z z' g) c d := by sorry
