-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCH_continuous_sL_apply
-- name    : PI.LevelKSplit.W.NCH.continuous_sL_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:26.607214+00:00
-- url     : https://prove2.me/theorems/e97f8b30-deb1-55f6-be39-2bcd4a1d1f63
-- title:
--   NCH: continuous s L apply
-- statement:
--   The NCH construction uses the continuous s L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCHeisC.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCHeisC.lean#L30-L44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCHeisC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} (P : Frame E M r) (T : F)

theorem PI.LevelKSplit.W.NCH.continuous_sL_apply (half : R ⊗[F] E) {X : Type} [TopologicalSpace X]
    {y : X → Fin r → Fin M → R ⊗[F] E} (hy : Continuous y) (v : Fin M → R ⊗[F] E) :
    Continuous fun x => sL (PI.VolSemiDirect.W.datR R σ J P T) half (y x) v := by sorry
