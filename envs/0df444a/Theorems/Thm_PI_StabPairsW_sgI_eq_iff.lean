-- Prove2me | Theorems.Thm_PI_StabPairsW_sgI_eq_iff
-- name    : PI.StabPairsW.sgI_eq_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:46:57.925804+00:00
-- url     : https://prove2.me/theorems/3bfa571d-8ce6-4d36-a3f7-df2436cf516d
-- title:
--   Stab Pairs W: sg I eq iff
-- statement:
--   The Stab Pairs W construction uses the sg I eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L33-L36

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

theorem PI.StabPairsW.sgI_eq_iff (i : Fin (2 * r + k + 1)) : sgI k r i.val = r + k ↔ i.val = r + k := by sorry
