-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_in
-- name    : PI.UnitaryGroupMassFormula.BesselLevi.hW_in
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:33.882011+00:00
-- url     : https://prove2.me/theorems/5a1a4ee5-8621-4269-a63c-cd0f85f59431
-- title:
--   Bessel Levi: h W in
-- statement:
--   The Bessel Levi construction uses the h W in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselLeviAction/MulVecBvecApply.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselLeviAction/MulVecBvecApply.lean#L119-L123

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

theorem PI.UnitaryGroupMassFormula.BesselLevi.hW_in {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {i j : Fin (2 * r + k + 1)} (hi : r ≤ i.val ∧ i.val ≤ r + k) (hj : r ≤ j.val ∧ j.val ≤ r + k) :
    hW k r s i j = s i j := by sorry
