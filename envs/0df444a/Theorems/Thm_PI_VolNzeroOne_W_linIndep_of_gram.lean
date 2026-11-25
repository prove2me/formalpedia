-- Prove2me | Theorems.Thm_PI_VolNzeroOne_W_linIndep_of_gram
-- name    : PI.VolNzeroOne.W.linIndep_of_gram
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:26.720211+00:00
-- url     : https://prove2.me/theorems/49c51539-5fee-44f6-9e99-9d0659b4f150
-- title:
--   W: lin Indep of gram
-- statement:
--   The W construction uses the lin Indep of gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L22-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L22-L46

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

theorem PI.VolNzeroOne.W.linIndep_of_gram {n M : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) (h : (gramE σ J X).det ≠ 0) : LinearIndependent E X := by sorry
