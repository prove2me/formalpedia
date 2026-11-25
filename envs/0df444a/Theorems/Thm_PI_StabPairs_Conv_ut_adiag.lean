-- Prove2me | Theorems.Thm_PI_StabPairs_Conv_ut_adiag
-- name    : PI.StabPairs.Conv.ut_adiag
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:39:37.225478+00:00
-- url     : https://prove2.me/theorems/bc250941-29e9-566a-a605-7f9ed3a3fe99
-- title:
--   Conv: ut adiag
-- statement:
--   The Conv construction uses the ut adiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/UtSubOneLast.lean#L64-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/UtSubOneLast.lean#L64-L77

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

theorem PI.StabPairs.Conv.ut_adiag (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hu : u ∈ UTset (r + 1)) : uᴴ * Adiag k r z * u = Adiag k r z := by sorry
