-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_levelS_of
-- name    : PI.LevelKSplit.W.levelS_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:26.967298+00:00
-- url     : https://prove2.me/theorems/931b8d16-d980-42aa-b021-1b4a64625ca4
-- title:
--   W: level S of
-- statement:
--   The W construction uses the level S of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOf.lean#L41-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOf.lean#L41-L108

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LevelKSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
variable {F E σ M J}

theorem PI.LevelKSplit.W.levelS_of (hinv : ∀ x, σ (σ x) = x) (hEx : ExistS F E σ M J) (hMe : MeasKf F E σ M J) (hSp : SplitK F E σ M J) :
    LevelS F E σ M J := by sorry
