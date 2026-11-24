-- Prove2me | Theorems.Thm_PI_StabPairs_Conv_gram_Km
-- name    : PI.StabPairs.Conv.gram_Km
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:31.122896+00:00
-- url     : https://prove2.me/theorems/ceec1f54-095f-4a1c-88a9-bd69f71dcc55
-- title:
--   Conv: gram Km
-- statement:
--   The Conv construction uses the gram Km property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/HermBvecFvec.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/HermBvecFvec.lean#L52-L57

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec
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

theorem PI.StabPairs.Conv.gram_Km (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (hGi : IsUnit (gramM k r z z' γ).det) (v : Fin (2 * r + k + 1) → ℂ) :
    gramM k r z z' γ *ᵥ (Km k r z z' γ *ᵥ v) = ((Fm k r z z' γ)ᴴ * Hpk k r) *ᵥ v := by sorry
