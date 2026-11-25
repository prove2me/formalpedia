-- Prove2me | Theorems.Thm_PI_StabPairsW_gramM_blocks
-- name    : PI.StabPairsW.gramM_blocks
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:54.859748+00:00
-- url     : https://prove2.me/theorems/4bd9d12a-2cb3-4d8e-adf1-93dfcaf4a938
-- title:
--   Stab Pairs W: gram M blocks
-- statement:
--   The Stab Pairs W construction uses the gram M blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L273-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L273-L285

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
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
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}

theorem PI.StabPairsW.gramM_blocks (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (γ : B.Mat k r)
    (hγ : γ ∈ B.GV k r) :
    gramM k r z z' γ = Matrix.fromBlocks (Adiag k r z) (Zhat k r z z' γ) (Zhat k r z z' γ)ᴴ (Adiag k r z') := by sorry
