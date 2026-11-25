-- Prove2me | Theorems.Thm_PI_Residue_mem_hit_of_mem_sub
-- name    : PI.Residue.mem_hit_of_mem_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:20:20.716609+00:00
-- url     : https://prove2.me/theorems/327a036c-9649-4837-8aa1-f4eda06489f0
-- title:
--   Residue: mem hit of mem sub
-- statement:
--   The Residue construction uses the mem hit of mem sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/NormAtPlacePosOfNormPos.lean#L54-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/NormAtPlacePosOfNormPos.lean#L54-L73

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

theorem PI.Residue.mem_hit_of_mem_sub {ρ : ℝ} {y x : mixedSpace K} (hy : 0 < mixedEmbedding.norm y)
    (hx : x ∈ box K (fun w => ρ / (2 * normAtPlace w y)) -
      box K (fun w => ρ / (2 * normAtPlace w y))) : y ∈ hit K ρ x := by sorry
