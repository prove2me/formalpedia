-- Prove2me | Theorems.Thm_PI_DegenerateSiegelWeil_Scale_hermMap_mul
-- name    : PI.DegenerateSiegelWeil.Scale.hermMap_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:15:46.584511+00:00
-- url     : https://prove2.me/theorems/1222f43c-e77b-4352-a848-a86446f01340
-- title:
--   Scale: herm Map mul
-- statement:
--   The Scale construction uses the herm Map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L123-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L123-L126

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n M : ℕ}

theorem PI.DegenerateSiegelWeil.Scale.hermMap_mul (hσ : ∀ x, σ (σ x) = x) (D₁ D₂ : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (S : HermR R σ n) : hermMap R σ hσ D₁ (hermMap R σ hσ D₂ S) = hermMap R σ hσ (D₂ * D₁) S := by sorry
