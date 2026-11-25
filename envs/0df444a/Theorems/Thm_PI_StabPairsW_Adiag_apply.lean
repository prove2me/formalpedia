-- Prove2me | Theorems.Thm_PI_StabPairsW_Adiag_apply
-- name    : PI.StabPairsW.Adiag_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:36.828301+00:00
-- url     : https://prove2.me/theorems/046ba83d-9cc7-4404-b375-eec578193083
-- title:
--   Stab Pairs W: Adiag apply
-- statement:
--   The Stab Pairs W construction uses the Adiag apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L263-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L263-L271

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

theorem PI.StabPairsW.Adiag_apply (z : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    Adiag k r z a b = if a = Fin.last r ∧ b = Fin.last r then herm (Hpk k r) z z else 0 := by sorry
