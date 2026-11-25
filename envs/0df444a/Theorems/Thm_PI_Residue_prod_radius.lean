-- Prove2me | Theorems.Thm_PI_Residue_prod_radius
-- name    : PI.Residue.prod_radius
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:23.617216+00:00
-- url     : https://prove2.me/theorems/8df86ba4-47f3-480e-ad5c-0012aa243fd3
-- title:
--   Residue: prod radius
-- statement:
--   The Residue construction uses the prod radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/NormAtPlacePosOfNormPos.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/NormAtPlacePosOfNormPos.lean#L46-L52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_LatticeCountGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NormAtPlacePosOfNormPos
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
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable (K : Type) [Field K] [NumberField K]
variable {K}

theorem PI.Residue.prod_radius (ρ : ℝ) (y : mixedSpace K) :
    ∏ w : InfinitePlace K, (ρ / (2 * normAtPlace w y)) ^ mult w
      = (ρ / 2) ^ Module.finrank ℚ K / mixedEmbedding.norm y := by sorry
