-- Prove2me | Theorems.Thm_PI_StabPairsW_herm_GV
-- name    : PI.StabPairsW.herm_GV
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:29:48.454351+00:00
-- url     : https://prove2.me/theorems/d70e2dec-f612-453f-9ce2-4bac62b3e9e0
-- title:
--   Stab Pairs W: herm GV
-- statement:
--   The Stab Pairs W construction uses the herm GV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L155-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L155-L159

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

theorem PI.StabPairsW.herm_GV {g : B.Mat k r} (hg : g ∈ B.GV k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by sorry
