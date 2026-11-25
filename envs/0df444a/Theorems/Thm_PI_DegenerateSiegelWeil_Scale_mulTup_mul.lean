-- Prove2me | Theorems.Thm_PI_DegenerateSiegelWeil_Scale_mulTup_mul
-- name    : PI.DegenerateSiegelWeil.Scale.mulTup_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:16:28.181188+00:00
-- url     : https://prove2.me/theorems/324e9f8a-885b-526e-bce3-71b07f652fde
-- title:
--   Scale: mul Tup mul
-- statement:
--   The Scale construction uses the mul Tup mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L18-L24

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

theorem PI.DegenerateSiegelWeil.Scale.mulTup_mul (D₁ D₂ : Matrix (Fin n) (Fin n) K) (X : Fin n → Fin M → K) :
    mulTup D₁ (mulTup D₂ X) = mulTup (D₂ * D₁) X := by sorry
