-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_tau_val
-- name    : PI.UnitaryGroupMassFormula.BesselLevi.tau_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:51.960316+00:00
-- url     : https://prove2.me/theorems/c2d4265e-c6cd-424b-afe8-e58b6a2bef43
-- title:
--   Bessel Levi: tau val
-- statement:
--   The Bessel Levi construction uses the tau val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselLeviAction/MulVecBvecApply.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselLeviAction/MulVecBvecApply.lean#L51-L52

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

theorem PI.UnitaryGroupMassFormula.BesselLevi.tau_val (i : Fin (2 * r + k + 1)) :
    (tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by sorry
