-- Prove2me | Theorems.Thm_PI_WeylForKWork_DimensionInduction_Good_inner
-- name    : PI.WeylForKWork.DimensionInduction.Good.inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:55.899219+00:00
-- url     : https://prove2.me/theorems/eb54f2c5-9c8f-4582-8e79-3a06548cb960
-- title:
--   Good: inner
-- statement:
--   The Good construction uses the inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/DimStepA.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/DimStepA.lean#L58-L60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork PI.WeylForKWork.DimensionInduction
open scoped InnerProductSpace
open Module
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*}
variable {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}

theorem PI.WeylForKWork.DimensionInduction.Good.inner (hρ : Good ρ) (i : ι) (x y : H) : ⟪ρ i x, ρ i y⟫_ℂ = ⟪x, y⟫_ℂ := by sorry
