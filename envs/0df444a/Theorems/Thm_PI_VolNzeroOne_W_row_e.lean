-- Prove2me | Theorems.Thm_PI_VolNzeroOne_W_row_e
-- name    : PI.VolNzeroOne.W.row_e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:00.026207+00:00
-- url     : https://prove2.me/theorems/77a08272-bef1-5577-84a2-3b9167b919dd
-- title:
--   W: row e
-- statement:
--   The W construction uses the row e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L152-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L152-L172

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

theorem PI.VolNzeroOne.W.row_e (hP : P.IsStd σ J T) (a : Fin r) :
    ∀ j, gramE σ J (tupH P) (Fin.castAdd r (Fin.castSucc a)) j =
      if j = Fin.natAdd (r + 1) a then 1 else 0 := by sorry
