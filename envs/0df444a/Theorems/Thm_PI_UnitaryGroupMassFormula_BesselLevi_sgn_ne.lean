-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_sgn_ne
-- name    : PI.UnitaryGroupMassFormula.BesselLevi.sgn_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:31:10.953575+00:00
-- url     : https://prove2.me/theorems/b084d6da-f367-4b5e-9f35-0bb54ef7aa96
-- title:
--   Bessel Levi: sgn ne
-- statement:
--   The Bessel Levi construction uses the sgn ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselLeviAction/MulVecBvecApply.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselLeviAction/MulVecBvecApply.lean#L57-L59

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

theorem PI.UnitaryGroupMassFormula.BesselLevi.sgn_ne (i : Fin (2 * r + k + 1)) : sgn k r i ≠ 0 := by sorry
