-- Prove2me | Theorems.Thm_PI_VolNzeroOne_W_if_inj
-- name    : PI.VolNzeroOne.W.if_inj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:11.291945+00:00
-- url     : https://prove2.me/theorems/e904860f-96ce-48a2-86c2-953f61a822a9
-- title:
--   W: if inj
-- statement:
--   The W construction uses the if inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L98-L102

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

theorem PI.VolNzeroOne.W.if_inj {r : ℕ} {a b : Fin r}
    (h : (Fin.natAdd (r + 1) a : Fin (r + 1 + r)) = Fin.natAdd (r + 1) b) : a = b := by sorry
