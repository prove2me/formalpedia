-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_local_unit
-- name    : PI.UnitaryApproxFinWork.local_unit
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:31.697092+00:00
-- url     : https://prove2.me/theorems/bb0db8b6-53d2-457a-9b9b-fa709f11618c
-- title:
--   Unitary Approx Fin Work: local unit
-- statement:
--   The Unitary Approx Fin Work construction uses the local unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/Assembly.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/Assembly.lean#L39-L51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SkewApprox
import Definitions.Def_Lemmata_GeneralBFactRightTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Assembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork

theorem PI.UnitaryApproxFinWork.local_unit {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (h2 : IsUnit (2 : R)) (g X XR W : Matrix n n R)
    (hXP : (1 + X) * (1 + g) = 2) (hΔ : (XR - X) * (1 + g) = (2 : R) • W) (hW : IsUnit (1 + W).det) :
    IsUnit (1 + XR).det := by sorry
