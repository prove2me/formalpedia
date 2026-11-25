-- Prove2me | Theorems.Thm_PI_Residue_count_pointwise
-- name    : PI.Residue.count_pointwise
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:19:33.057984+00:00
-- url     : https://prove2.me/theorems/bb2f75ed-fb61-47e3-b11e-0aacf9c9bb5a
-- title:
--   Residue: count pointwise
-- statement:
--   The Residue construction uses the count pointwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/NormAtPlacePosOfNormPos.lean#L75-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/NormAtPlacePosOfNormPos.lean#L75-L98

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

theorem PI.Residue.count_pointwise (hB : BoxVolume) (J : (Ideal (𝓞 K))⁰) {ρ : ℝ} (hρ : 0 < ρ)
    {y : mixedSpace K} (hy : y ∈ shell K) :
    vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) ≤
      (∑' x : lat K J, (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y) *
        ENNReal.ofReal (ZLattice.covolume (lat K J)) := by sorry
