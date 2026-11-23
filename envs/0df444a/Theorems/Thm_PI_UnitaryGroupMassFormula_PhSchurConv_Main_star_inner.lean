-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhSchurConv_Main_star_inner
-- name    : PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:45:45.313845+00:00
-- url     : https://prove2.me/theorems/995e347b-7571-44c2-8934-976aa256d33c
-- title:
--   Main: star inner
-- statement:
--   The Main construction uses the star inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurConvolution/MapMulApply.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurConvolution/MapMulApply.lean#L13-L15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhSchurConv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurConvolution_MapMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhSchurConv PI.UnitaryGroupMassFormula.PhSchurConv.Main
open PI.PhSchurConv

theorem PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (a b : H) :
    star ⟪a, b⟫_ℂ = ⟪b, a⟫_ℂ := by sorry
