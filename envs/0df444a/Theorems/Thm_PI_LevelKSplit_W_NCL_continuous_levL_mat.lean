-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_continuous_levL_mat
-- name    : PI.LevelKSplit.W.NCL.continuous_levL_mat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:40:17.776027+00:00
-- url     : https://prove2.me/theorems/08209b6e-afcb-5554-bafd-d7ff36803f67
-- title:
--   NCL: continuous lev L mat
-- statement:
--   The NCL construction uses the continuous lev L mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousLevLMat.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousLevLMat.lean#L35-L42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_IsClosedAsub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousLevLMat
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}

theorem PI.LevelKSplit.W.NCL.continuous_levL_mat (T : F) (P : Frame E M r) {X : Type} [TopologicalSpace X]
    {U W : X → Matrix (Fin r) (Fin r) (Af F ⊗[F] E)}
    (hU : ∀ a b, Continuous fun x => U x a b) (hW : ∀ a b, Continuous fun x => W x a b) :
    Continuous fun x => LinearMap.toMatrix' (levL (datR (Af F) σ J P T) (U x) (W x)) := by sorry
