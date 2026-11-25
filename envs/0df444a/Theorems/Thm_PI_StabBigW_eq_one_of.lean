-- Prove2me | Theorems.Thm_PI_StabBigW_eq_one_of
-- name    : PI.StabBigW.eq_one_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:27:21.363852+00:00
-- url     : https://prove2.me/theorems/8a052b7c-f2c1-4f82-bf76-e37242bef8fb
-- title:
--   Stab Big W: eq one of
-- statement:
--   The Stab Big W construction uses the eq one of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L359-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L359-L418

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

theorem PI.StabBigW.eq_one_of {c : Fin r → ℂ} {μ L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hc : ∀ a, c a ≠ 0) (hL : μ * L = 1)
    {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : UT k r a) (hb : UT k r b) (E : a * bigCell k r c μ = bigCell k r c μ * b) : a = 1 := by sorry
