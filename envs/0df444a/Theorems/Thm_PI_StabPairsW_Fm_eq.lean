-- Prove2me | Theorems.Thm_PI_StabPairsW_Fm_eq
-- name    : PI.StabPairsW.Fm_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:46:43.126013+00:00
-- url     : https://prove2.me/theorems/1ca0951e-0ee4-4af4-a6f7-8850c2d6ddcc
-- title:
--   Stab Pairs W: Fm eq
-- statement:
--   The Stab Pairs W construction uses the Fm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L111-L114

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

theorem PI.StabPairsW.Fm_eq (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Fm k r z z' γ = Matrix.fromCols (Ff k r z) (γ * Ff k r z') := by sorry
