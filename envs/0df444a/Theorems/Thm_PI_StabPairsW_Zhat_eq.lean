-- Prove2me | Theorems.Thm_PI_StabPairsW_Zhat_eq
-- name    : PI.StabPairsW.Zhat_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:30:23.074063+00:00
-- url     : https://prove2.me/theorems/64cdc9fb-edec-5525-9542-424c643df84a
-- title:
--   Stab Pairs W: Zhat eq
-- statement:
--   The Stab Pairs W construction uses the Zhat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L139-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L139-L148

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

theorem PI.StabPairsW.Zhat_eq (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Zhat k r z z' γ = (Ff k r z)ᴴ * Hpk k r * γ * Ff k r z' := by sorry
