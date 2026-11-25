-- Prove2me | Theorems.Thm_PI_StabPairs_Conv_ut_det
-- name    : PI.StabPairs.Conv.ut_det
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:09.645869+00:00
-- url     : https://prove2.me/theorems/3d0262e0-9363-4cee-b2f0-e9c061806b8c
-- title:
--   Conv: ut det
-- statement:
--   The Conv construction uses the ut det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/UtSubOneLast.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/UtSubOneLast.lean#L18-L20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConvAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
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
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

theorem PI.StabPairs.Conv.ut_det {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) : u.det = 1 := by sorry
