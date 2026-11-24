-- Prove2me | Theorems.Thm_PI_StabPairsW_herm_bvec
-- name    : PI.StabPairsW.herm_bvec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:29:27.232799+00:00
-- url     : https://prove2.me/theorems/387fc95f-83da-4dd3-800c-e0210bfeabd1
-- title:
--   Stab Pairs W: herm bvec
-- statement:
--   The Stab Pairs W construction uses the herm bvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L172-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L172-L174

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

theorem PI.StabPairsW.herm_bvec (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) v (bvec j) = (Hpk k r *ᵥ v) j := by sorry
