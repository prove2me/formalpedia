-- Prove2me | Theorems.Thm_PI_StabPairsW_mul_of_col
-- name    : PI.StabPairsW.mul_of_col
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:52:04.37635+00:00
-- url     : https://prove2.me/theorems/327e12ae-98ef-4b0b-bc61-46ca186a7dc5
-- title:
--   Stab Pairs W: mul of col
-- statement:
--   The Stab Pairs W construction uses the mul of col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean#L14-L20

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

theorem PI.StabPairsW.mul_of_col (z : Fin (2 * r + k + 1) → ℂ) (s : B.Mat k r) (x : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (h : ∀ b, s *ᵥ fvec k r z b = ∑ c, x c b • fvec k r z c) : s * Ff k r z = Ff k r z * x := by sorry
