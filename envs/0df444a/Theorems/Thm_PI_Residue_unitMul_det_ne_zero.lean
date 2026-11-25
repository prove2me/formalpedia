-- Prove2me | Theorems.Thm_PI_Residue_unitMul_det_ne_zero
-- name    : PI.Residue.unitMul_det_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:19:55.331791+00:00
-- url     : https://prove2.me/theorems/8a78cfe5-a35b-4212-8422-f8d68de0e708
-- title:
--   Residue: unit Mul det ne zero
-- statement:
--   The Residue construction uses the unit Mul det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/UnitMulDetNeZero.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/UnitMulDetNeZero.lean#L24-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BoxEqConvexBodyLT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitMulDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable (K : Type) [Field K] [NumberField K]

theorem PI.Residue.unitMul_det_ne_zero (u : (𝓞 K)ˣ) : LinearMap.det (unitMul K u) ≠ 0 := by sorry
