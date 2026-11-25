-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiA_ext_lin
-- name    : PI.LevelKSplit.W.SemiA.ext_lin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:27:23.808256+00:00
-- url     : https://prove2.me/theorems/24bfceec-a964-4765-94c2-f7f8dd2f9b75
-- title:
--   Semi A: ext lin
-- statement:
--   The Semi A construction uses the ext lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ToMatrixLin.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ToMatrixLin.lean#L49-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem PI.LevelKSplit.W.SemiA.ext_lin {g g' : HA R σ J} (h : ∀ v, lin R σ J g v = lin R σ J g' v) : g = g' := by sorry
