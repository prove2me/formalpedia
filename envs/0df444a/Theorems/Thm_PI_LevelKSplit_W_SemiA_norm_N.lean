-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiA_norm_N
-- name    : PI.LevelKSplit.W.SemiA.norm_N
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:27:47.710046+00:00
-- url     : https://prove2.me/theorems/6145637b-fe74-4865-812e-a8eeb3ec95d1
-- title:
--   Semi A: norm N
-- statement:
--   The Semi A construction uses the norm N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ToMatrixLin.lean#L108-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ToMatrixLin.lean#L108-L140

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

theorem PI.LevelKSplit.W.SemiA.norm_N {h n : HA R σ J} (hh : h ∈ Hsub R σ J P) (hn : n ∈ Nsub R σ J P) :
    h * n * h⁻¹ ∈ Nsub R σ J P := by sorry
