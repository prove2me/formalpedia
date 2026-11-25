-- Prove2me | Theorems.Thm_PI_DegenerateSiegelWeil_Scale_hermMap_coe
-- name    : PI.DegenerateSiegelWeil.Scale.hermMap_coe
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:16:23.893597+00:00
-- url     : https://prove2.me/theorems/c7858738-a585-462e-bb17-407e20a73534
-- title:
--   Scale: herm Map coe
-- statement:
--   The Scale construction uses the herm Map coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L119-L121

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

theorem PI.DegenerateSiegelWeil.Scale.hermMap_coe (hσ : ∀ x, σ (σ x) = x) (D : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (S : HermR R σ n) :
    (hermMap R σ hσ D S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = conjT R σ D * S * D := by sorry
