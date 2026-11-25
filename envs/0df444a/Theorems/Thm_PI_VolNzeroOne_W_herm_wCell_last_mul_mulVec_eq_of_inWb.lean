-- Prove2me | Theorems.Thm_PI_VolNzeroOne_W_herm_wCell_last_mul_mulVec_eq_of_inWb
-- name    : PI.VolNzeroOne.W.herm_wCell_last_mul_mulVec_eq_of_inWb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:07.260466+00:00
-- url     : https://prove2.me/theorems/a3a2453f-dea7-434a-8931-533883daf832
-- title:
--   W: herm w Cell last mul mul Vec eq of in Wb
-- statement:
--   The W construction uses the herm w Cell last mul mul Vec eq of in Wb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L130-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L130-L150

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

theorem PI.VolNzeroOne.W.herm_wCell_last_mul_mulVec_eq_of_inWb (hP : P.IsStd σ J T)
    (hT1 : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) :
    ∀ j, gramE σ J (tupH P) (Fin.castAdd r (Fin.last r)) j =
      if j = Fin.castAdd r (Fin.last r) then algebraMap F E (-T) else 0 := by sorry
