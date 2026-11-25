-- Prove2me | Theorems.Thm_PI_StabPairsW_Fm_conjTranspose
-- name    : PI.StabPairsW.Fm_conjTranspose
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:33.140616+00:00
-- url     : https://prove2.me/theorems/07e02c57-8e31-4081-9b2b-ade604b5829f
-- title:
--   Stab Pairs W: Fm conj Transpose
-- statement:
--   The Stab Pairs W construction uses the Fm conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L116-L119

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

theorem PI.StabPairsW.Fm_conjTranspose (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    (Fm k r z z' γ)ᴴ = Matrix.of fun i j => star (gramVec k r z z' γ i j) := by sorry
