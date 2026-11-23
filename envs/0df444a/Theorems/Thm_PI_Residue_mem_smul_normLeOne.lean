-- Prove2me | Theorems.Thm_PI_Residue_mem_smul_normLeOne
-- name    : PI.Residue.mem_smul_normLeOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:08.508211+00:00
-- url     : https://prove2.me/theorems/51f2deef-d4ef-45ec-9919-bfb3d6e97f74
-- title:
--   Residue: mem smul norm Le One
-- statement:
--   The Residue construction uses the mem smul norm Le One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/MemSmulNormLeOne.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/MemSmulNormLeOne.lean#L24-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_MemSmulNormLeOne
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

theorem PI.Residue.mem_smul_normLeOne (y : mixedSpace K) :
    y ∈ cHalf K • normLeOne K ↔ y ∈ fundamentalCone K ∧ mixedEmbedding.norm y ≤ 1 / 2 := by sorry
