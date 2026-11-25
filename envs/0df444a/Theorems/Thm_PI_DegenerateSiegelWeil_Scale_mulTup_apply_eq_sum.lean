-- Prove2me | Theorems.Thm_PI_DegenerateSiegelWeil_Scale_mulTup_apply_eq_sum
-- name    : PI.DegenerateSiegelWeil.Scale.mulTup_apply_eq_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:16:31.639536+00:00
-- url     : https://prove2.me/theorems/f95265e9-771d-5f5e-92ae-bacce0f61a2c
-- title:
--   Scale: mul Tup apply eq sum
-- statement:
--   The Scale construction uses the mul Tup apply eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L35-L38

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

theorem PI.DegenerateSiegelWeil.Scale.mulTup_apply_eq_sum (D : Matrix (Fin n) (Fin n) K) (X : Fin n → Fin M → K) (j : Fin n) :
    mulTup D X j = ∑ k, D k j • X k := by sorry
