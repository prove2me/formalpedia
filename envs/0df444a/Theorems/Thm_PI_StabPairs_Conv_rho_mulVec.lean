-- Prove2me | Theorems.Thm_PI_StabPairs_Conv_rho_mulVec
-- name    : PI.StabPairs.Conv.rho_mulVec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:00:54.456915+00:00
-- url     : https://prove2.me/theorems/e3d8b32b-eccf-4738-89e0-f2f09b9074cc
-- title:
--   Conv: rho mul Vec
-- statement:
--   The Conv construction uses the rho mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/HermBvecFvec.lean#L31-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/HermBvecFvec.lean#L31-L50

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

theorem PI.StabPairs.Conv.rho_mulVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    PI.StabPairsW.rhoOf k r z z' γ u u' *ᵥ v =
      v + Ff k r z *ᵥ ((u - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inl)) +
        (γ * Ff k r z') *ᵥ ((u' - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inr)) := by sorry
