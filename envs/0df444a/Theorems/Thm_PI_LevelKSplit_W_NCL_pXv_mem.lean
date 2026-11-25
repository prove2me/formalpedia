-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_pXv_mem
-- name    : PI.LevelKSplit.W.NCL.pXv_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:38.205001+00:00
-- url     : https://prove2.me/theorems/0fa8fe42-5341-4f61-bd33-77b40b2f8ecd
-- title:
--   NCL: p Xv mem
-- statement:
--   The NCL construction uses the p Xv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LeviInfUnipotentEqOne.lean#L210-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LeviInfUnipotentEqOne.lean#L210-L212

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
variable {R σ J P T}
variable (R σ J P)
variable {R σ J P}

theorem PI.LevelKSplit.W.NCL.pXv_mem (x : Fin M → R ⊗[F] E) :
    (datR R σ J P T).pXv x ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.f a)) := by sorry
