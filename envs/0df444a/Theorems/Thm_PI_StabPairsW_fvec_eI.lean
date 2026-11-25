-- Prove2me | Theorems.Thm_PI_StabPairsW_fvec_eI
-- name    : PI.StabPairsW.fvec_eI
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:29.488901+00:00
-- url     : https://prove2.me/theorems/c39b75b8-9aaa-47f7-ada4-8f2ac39a8cfa
-- title:
--   Stab Pairs W: fvec e I
-- statement:
--   The Stab Pairs W construction uses the fvec e I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L210-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L210-L219

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

theorem PI.StabPairsW.fvec_eI (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : Fin (r + 1)) (a : Fin r) :
    fvec k r z c (eI k r a) = if c.val = a.val then 1 else 0 := by sorry
