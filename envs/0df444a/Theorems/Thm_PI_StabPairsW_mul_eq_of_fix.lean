-- Prove2me | Theorems.Thm_PI_StabPairsW_mul_eq_of_fix
-- name    : PI.StabPairsW.mul_eq_of_fix
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:05:03.086279+00:00
-- url     : https://prove2.me/theorems/93ccffb9-4499-5ed0-bcf9-38e6393ea845
-- title:
--   Stab Pairs W: mul eq of fix
-- statement:
--   The Stab Pairs W construction uses the mul eq of fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean#L190-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean#L190-L205

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
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

theorem PI.StabPairsW.mul_eq_of_fix (z z' : Fin (2 * r + k + 1) → ℂ) (γ ρ : B.Mat k r)
    (hfix : ∀ v ∈ Uperp k r z z' γ, ρ *ᵥ v = v) {ι : Type*} (Q : Matrix (Fin (2 * r + k + 1)) ι ℂ)
    (hQ : ((Fm k r z z' γ)ᴴ * Hpk k r) * Q = 0) : ρ * Q = Q := by sorry
