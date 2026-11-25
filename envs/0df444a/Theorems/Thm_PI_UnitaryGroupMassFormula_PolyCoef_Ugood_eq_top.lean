-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Ugood_eq_top
-- name    : PI.UnitaryGroupMassFormula.PolyCoef.Ugood_eq_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:16.078815+00:00
-- url     : https://prove2.me/theorems/8245bc74-79db-4a88-8776-8da73813ebdb
-- title:
--   Poly Coef: Ugood eq top
-- statement:
--   The Poly Coef construction uses the Ugood eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/IsPositiveDefiniteMatrixCoefficientOfMemAlgA.lean#L101-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/IsPositiveDefiniteMatrixCoefficientOfMemAlgA.lean#L101-L176

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

theorem PI.UnitaryGroupMassFormula.PolyCoef.Ugood_eq_top (hrep : IsURepOn (Kset (allPos N)) σ) (hfin : FiniteDimensional ℂ S)
    (hst : IsKStableOn (allPos N) σ S) : Ugood σ S = ⊤ := by sorry
