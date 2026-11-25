-- Prove2me | Theorems.Thm_PI_StabPairs_Conv_cancel_of_pair
-- name    : PI.StabPairs.Conv.cancel_of_pair
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:01.467381+00:00
-- url     : https://prove2.me/theorems/770fce22-40a5-448e-ada7-01903ffae1d7
-- title:
--   Conv: cancel of pair
-- statement:
--   The Conv construction uses the cancel of pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/UtSubOneLast.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/UtSubOneLast.lean#L52-L62

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

theorem PI.StabPairs.Conv.cancel_of_pair {r : ℕ} {u u' Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (hZ : IsUnit Z.det) (hp : uᴴ * Z * u' = Z) (c : Fin (r + 1) → ℂ)
    (hc : ∀ a : Fin (r + 1), a.val < r → (Z *ᵥ c) a = 0) : (u' - 1) *ᵥ c = 0 := by sorry
