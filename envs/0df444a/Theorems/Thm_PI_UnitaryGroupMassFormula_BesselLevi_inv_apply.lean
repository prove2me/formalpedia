-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_inv_apply
-- name    : PI.UnitaryGroupMassFormula.BesselLevi.inv_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:32:35.014107+00:00
-- url     : https://prove2.me/theorems/7ff4ac32-e53b-47a4-b0cb-09987d78d8c3
-- title:
--   Bessel Levi: inv apply
-- statement:
--   The Bessel Levi construction uses the inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselLeviAction/MulVecBvecApply.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselLeviAction/MulVecBvecApply.lean#L80-L84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselLevi
variable {k r : ℕ}

theorem PI.UnitaryGroupMassFormula.BesselLevi.inv_apply {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) (p q : Fin (2 * r + k + 1)) :
    s⁻¹ p q = sgn k r p * (star (s (tau k r q) (tau k r p)) * sgn k r q) := by sorry
