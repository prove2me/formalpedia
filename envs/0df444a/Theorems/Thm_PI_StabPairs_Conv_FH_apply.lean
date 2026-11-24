-- Prove2me | Theorems.Thm_PI_StabPairs_Conv_FH_apply
-- name    : PI.StabPairs.Conv.FH_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:43.285331+00:00
-- url     : https://prove2.me/theorems/348f5f6f-b929-477b-9826-2f07f58b2636
-- title:
--   Conv: FH apply
-- statement:
--   The Conv construction uses the FH apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/HermBvecFvec.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/HermBvecFvec.lean#L59-L63

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

theorem PI.StabPairs.Conv.FH_apply (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ)
    (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (((Fm k r z z' γ)ᴴ * Hpk k r) *ᵥ v) j = herm (Hpk k r) v (gramVec k r z z' γ j) := by sorry
