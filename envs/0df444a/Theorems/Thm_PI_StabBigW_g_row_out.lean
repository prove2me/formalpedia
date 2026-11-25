-- Prove2me | Theorems.Thm_PI_StabBigW_g_row_out
-- name    : PI.StabBigW.g_row_out
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:21.818365+00:00
-- url     : https://prove2.me/theorems/bdc6add4-4eff-4b98-b0a2-d30e8b80b833
-- title:
--   Stab Big W: g row out
-- statement:
--   The Stab Big W construction uses the g row out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L243-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L243-L259

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

theorem PI.StabBigW.g_row_out (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i m : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    bigCell k r c μ i m = if m = tau k r i then dd k r c (tau k r i) else 0 := by sorry
