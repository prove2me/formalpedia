-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_cT_add
-- name    : PI.UnitaryApproxFinWork.cT_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:41.097208+00:00
-- url     : https://prove2.me/theorems/72722ba8-a18e-4f95-8169-f9e5e4948c5d
-- title:
--   Unitary Approx Fin Work: c T add
-- statement:
--   The Unitary Approx Fin Work construction uses the c T add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/Cayley.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/Cayley.lean#L12-L14

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

theorem PI.UnitaryApproxFinWork.cT_add (M N : Matrix n n A) : PI.UnitaryApproxDefs.cT ρ (M + N) = PI.UnitaryApproxDefs.cT ρ M + PI.UnitaryApproxDefs.cT ρ N := by sorry
