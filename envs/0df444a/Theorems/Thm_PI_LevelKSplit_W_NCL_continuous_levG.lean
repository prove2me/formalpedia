-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_continuous_levG
-- name    : PI.LevelKSplit.W.NCL.continuous_levG
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:36.40374+00:00
-- url     : https://prove2.me/theorems/93b5b620-bf35-497b-a03a-1277c6cab631
-- title:
--   NCL: continuous lev G
-- statement:
--   The NCL construction uses the continuous lev G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousLevLMat.lean#L44-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousLevLMat.lean#L44-L79

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

theorem PI.LevelKSplit.W.NCL.continuous_levG (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (P : Frame E M r) (T : F)
    (hP : P.IsStd σ J T) : Continuous (levG (R := Af F) hσσ hJ hP) := by sorry
