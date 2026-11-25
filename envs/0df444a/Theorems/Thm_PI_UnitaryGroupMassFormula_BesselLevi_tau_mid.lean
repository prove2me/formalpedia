-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_tau_mid
-- name    : PI.UnitaryGroupMassFormula.BesselLevi.tau_mid
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:31:05.554838+00:00
-- url     : https://prove2.me/theorems/deb33595-4f04-465f-81fd-db8a4f41baa8
-- title:
--   Bessel Levi: tau mid
-- statement:
--   The Bessel Levi construction uses the tau mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselLeviAction/MulVecBvecApply.lean#L54-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselLeviAction/MulVecBvecApply.lean#L54-L55

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

theorem PI.UnitaryGroupMassFormula.BesselLevi.tau_mid (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val ∧ i.val ≤ r + k) : tau k r i = i := by sorry
