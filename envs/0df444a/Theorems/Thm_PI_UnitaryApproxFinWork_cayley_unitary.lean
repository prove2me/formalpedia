-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_cayley_unitary
-- name    : PI.UnitaryApproxFinWork.cayley_unitary
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:31:28.459566+00:00
-- url     : https://prove2.me/theorems/7c2a5320-b3f9-47ec-8fab-e5edecf59093
-- title:
--   Unitary Approx Fin Work: cayley unitary
-- statement:
--   The Unitary Approx Fin Work construction uses the cayley unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/Cayley.lean#L20-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/Cayley.lean#L20-L38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Cayley
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.UnitaryApproxFinWork
variable {n : Type} [Fintype n] [DecidableEq n] {A : Type} [CommRing A] (ρ : A →+* A)

theorem PI.UnitaryApproxFinWork.cayley_unitary (J X : Matrix n n A) (hX : PI.UnitaryApproxDefs.cT ρ X * J + J * X = 0)
    (hQ : IsUnit (1 + X).det) :
    PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹) * J * ((1 - X) * (1 + X)⁻¹) = J := by sorry
