-- Prove2me | Theorems.Thm_PI_StabPairs_Conv_ut_conj_fix
-- name    : PI.StabPairs.Conv.ut_conj_fix
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:39:10.359874+00:00
-- url     : https://prove2.me/theorems/41d7c15c-46b9-44e1-9dc9-1990b30f008c
-- title:
--   Conv: ut conj fix
-- statement:
--   The Conv construction uses the ut conj fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/UtSubOneLast.lean#L38-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/UtSubOneLast.lean#L38-L50

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

theorem PI.StabPairs.Conv.ut_conj_fix {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (v : Fin (r + 1) → ℂ) (hv : ∀ a : Fin (r + 1), a.val < r → v a = 0) : uᴴ *ᵥ v = v := by sorry
