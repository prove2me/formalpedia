-- Prove2me | Theorems.Thm_PI_StabBigW_g_left_inv
-- name    : PI.StabBigW.g_left_inv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:27:35.246605+00:00
-- url     : https://prove2.me/theorems/736b33ef-f31d-442e-83ac-bc325132f5c6
-- title:
--   Stab Big W: g left inv
-- statement:
--   The Stab Big W construction uses the g left inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L325-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L325-L357

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

theorem PI.StabBigW.g_left_inv {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) {μ L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hL : L * μ = 1) : bigCell k r (fun a => star (c a)) L * bigCell k r c μ = 1 := by sorry
