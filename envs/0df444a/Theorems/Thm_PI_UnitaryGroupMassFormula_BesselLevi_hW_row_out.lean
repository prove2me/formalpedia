-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_row_out
-- name    : PI.UnitaryGroupMassFormula.BesselLevi.hW_row_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:55.432943+00:00
-- url     : https://prove2.me/theorems/2439f554-cb91-4b6e-8942-adfb599ff391
-- title:
--   Bessel Levi: h W row out
-- statement:
--   The Bessel Levi construction uses the h W row out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselLeviAction/MulVecBvecApply.lean#L131-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselLeviAction/MulVecBvecApply.lean#L131-L135

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

theorem PI.UnitaryGroupMassFormula.BesselLevi.hW_row_out {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (i j : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    hW k r s i j = if i = j then 1 else 0 := by sorry
