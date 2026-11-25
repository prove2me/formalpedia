-- Prove2me | Theorems.Thm_PI_VolNzeroOne_W_gram_frame_with_normal_eq_diag
-- name    : PI.VolNzeroOne.W.gram_frame_with_normal_eq_diag
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:35.957839+00:00
-- url     : https://prove2.me/theorems/942d0c4e-7f27-5c35-91a0-6c394afd2f65
-- title:
--   W: gram frame with normal eq diag
-- statement:
--   The W construction uses the gram frame with normal eq diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L201-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L201-L228

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolNzeroOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NilpotentVolumeOne_LinearIndependentFrameWithNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolNzeroOne PI.VolNzeroOne.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {M r : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (P : Frame E M r) (T : F)

theorem PI.VolNzeroOne.W.gram_frame_with_normal_eq_diag (hP : P.IsStd σ J T)
    (hT0 : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) :
    ∀ i j, gramE σ J (F0 P) i j =
      if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0 := by sorry
