-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_isPositiveDefinite_matrix_coefficient_of_mem_algA
-- name    : PI.UnitaryGroupMassFormula.PolyCoef.isPositiveDefinite_matrix_coefficient_of_mem_algA
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:13:02.733505+00:00
-- url     : https://prove2.me/theorems/14d33078-f385-4f5c-a9c9-9707e596f534
-- title:
--   Poly Coef: is Positive Definite matrix coefficient of mem alg A
-- statement:
--   The Poly Coef construction uses the is Positive Definite matrix coefficient of mem alg A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/IsPositiveDefiniteMatrixCoefficientOfMemAlgA.lean#L61-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/IsPositiveDefiniteMatrixCoefficientOfMemAlgA.lean#L61-L85

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_IsPositiveDefiniteMatrixCoefficientOfMemAlgA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}

theorem PI.UnitaryGroupMassFormula.PolyCoef.isPositiveDefinite_matrix_coefficient_of_mem_algA [FiniteDimensional ℂ S] (hrep : IsURepOn (Kset (allPos N)) σ) (hst : IsKStableOn (allPos N) σ S)
    {f : C(UG N, ℂ)} (hf : f ∈ algA N) (u : S) (w : H) :
    IsPD (fun h : UG N => ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ) := by sorry
