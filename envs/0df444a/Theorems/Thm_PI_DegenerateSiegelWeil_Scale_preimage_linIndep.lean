-- Prove2me | Theorems.Thm_PI_DegenerateSiegelWeil_Scale_preimage_linIndep
-- name    : PI.DegenerateSiegelWeil.Scale.preimage_linIndep
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:47.364319+00:00
-- url     : https://prove2.me/theorems/a568934d-be74-4fd8-8ddf-1d8b460da6f3
-- title:
--   Scale: preimage lin Indep
-- statement:
--   The Scale construction uses the preimage lin Indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L59-L68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_IsFibreFamilyReindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DegenerateSiegelWeil PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW
open scoped ENNReal NNReal TensorProduct Matrix
variable {K : Type} [CommRing K] {n M : ℕ}

theorem PI.DegenerateSiegelWeil.Scale.preimage_linIndep (D : (Matrix (Fin n) (Fin n) K)ˣ) :
    mulTup (M := M) (D : Matrix (Fin n) (Fin n) K) ⁻¹' {X | LinearIndependent K X} =
      {X | LinearIndependent K X} := by sorry
