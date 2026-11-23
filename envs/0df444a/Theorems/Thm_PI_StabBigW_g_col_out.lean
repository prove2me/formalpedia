-- Prove2me | Theorems.Thm_PI_StabBigW_g_col_out
-- name    : PI.StabBigW.g_col_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:13.432838+00:00
-- url     : https://prove2.me/theorems/fbcf0f9e-5e8b-4c9a-ab0c-c8229d46ce2a
-- title:
--   Stab Big W: g col out
-- statement:
--   The Stab Big W construction uses the g col out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L207-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L207-L223

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
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
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}

theorem PI.StabBigW.g_col_out (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) :
    bigCell k r c μ i j = if i = tau k r j then dd k r c j else 0 := by sorry
