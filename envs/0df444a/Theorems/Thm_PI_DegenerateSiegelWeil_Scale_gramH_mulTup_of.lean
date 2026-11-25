-- Prove2me | Theorems.Thm_PI_DegenerateSiegelWeil_Scale_gramH_mulTup_of
-- name    : PI.DegenerateSiegelWeil.Scale.gramH_mulTup_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:16:25.472473+00:00
-- url     : https://prove2.me/theorems/653aa634-fb80-427f-9a6c-bb8556429caa
-- title:
--   Scale: gram H mul Tup of
-- statement:
--   The Scale construction uses the gram H mul Tup of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L148-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L148-L156

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

theorem PI.DegenerateSiegelWeil.Scale.gramH_mulTup_of (hG : GramMulTup) {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    PI.VolStabSW.gramH R σ hσ J hJ (mulTup D X) =
      hermMap R σ hσ D (PI.VolStabSW.gramH R σ hσ J hJ X) := by sorry
