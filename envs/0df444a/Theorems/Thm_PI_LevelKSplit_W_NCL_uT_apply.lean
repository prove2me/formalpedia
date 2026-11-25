-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_uT_apply
-- name    : PI.LevelKSplit.W.NCL.uT_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:42.14451+00:00
-- url     : https://prove2.me/theorems/e1179da5-24f0-4cc7-b39f-b54e70efe339
-- title:
--   NCL: u T apply
-- statement:
--   The NCL construction uses the u T apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LeviInfUnipotentEqOne.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LeviInfUnipotentEqOne.lean#L23-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

theorem PI.LevelKSplit.W.NCL.uT_apply (g : HA R σ J) (a b : Fin r) : uT R σ J P g a b = if a < b then
    hR R σ J (ratV (F := F) R (P.f a)) (lin R σ J g (ratV (F := F) R (P.e b)))
    else if a = b then 1 else 0 := by sorry
