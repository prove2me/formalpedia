-- Prove2me | Theorems.Thm_PI_StabBigW_adj_apply
-- name    : PI.StabBigW.adj_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:27:27.298037+00:00
-- url     : https://prove2.me/theorems/13ee4041-ceb9-4922-8455-1784c7b796a6
-- title:
--   Stab Big W: adj apply
-- statement:
--   The Stab Big W construction uses the adj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L87-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L87-L97

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

theorem PI.StabBigW.adj_apply (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (p q : Fin (2 * r + k + 1)) :
    (Hpk k r * aᴴ * Hpk k r) p q = sgn k r p * sgn k r q * star (a (tau k r q) (tau k r p)) := by sorry
