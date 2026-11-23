-- Prove2me | Theorems.Thm_PI_Residue_mem_lat
-- name    : PI.Residue.mem_lat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:07.417802+00:00
-- url     : https://prove2.me/theorems/e0cee2fc-9b5e-4c56-a98d-2c30051e6c39
-- title:
--   Residue: mem lat
-- statement:
--   The Residue construction uses the mem lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean#L14-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold
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
variable {K : Type} [Field K] [NumberField K]

theorem PI.Residue.mem_lat {J : (Ideal (𝓞 K))⁰} {x : mixedSpace K} :
    x ∈ lat K J ↔ ∃ a : 𝓞 K, a ∈ (J : Ideal (𝓞 K)) ∧ mixedEmbedding K (a : K) = x := by sorry
