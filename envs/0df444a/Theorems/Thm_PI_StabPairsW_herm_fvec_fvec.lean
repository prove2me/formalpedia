-- Prove2me | Theorems.Thm_PI_StabPairsW_herm_fvec_fvec
-- name    : PI.StabPairsW.herm_fvec_fvec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:50.093792+00:00
-- url     : https://prove2.me/theorems/b4863732-a6c0-475b-9a0b-4f0f93aca766
-- title:
--   Stab Pairs W: herm fvec fvec
-- statement:
--   The Stab Pairs W construction uses the herm fvec fvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L247-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L247-L256

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

theorem PI.StabPairsW.herm_fvec_fvec (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z b) (fvec k r z a) =
      if a = Fin.last r ∧ b = Fin.last r then herm (Hpk k r) z z else 0 := by sorry
