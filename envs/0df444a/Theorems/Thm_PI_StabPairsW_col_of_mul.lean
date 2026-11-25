-- Prove2me | Theorems.Thm_PI_StabPairsW_col_of_mul
-- name    : PI.StabPairsW.col_of_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:57.882794+00:00
-- url     : https://prove2.me/theorems/80fe0b35-45bf-47db-bbf8-564c8c706dd2
-- title:
--   Stab Pairs W: col of mul
-- statement:
--   The Stab Pairs W construction uses the col of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L306-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L306-L313

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

theorem PI.StabPairsW.col_of_mul (z : Fin (2 * r + k + 1) → ℂ) (s : B.Mat k r) (x : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (h : s * Ff k r z = Ff k r z * x) (b : Fin (r + 1)) : s *ᵥ fvec k r z b = ∑ c, x c b • fvec k r z c := by sorry
