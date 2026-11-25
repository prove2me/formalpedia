-- Prove2me | Theorems.Thm_PI_VolNzeroOne_W_ie_inj
-- name    : PI.VolNzeroOne.W.ie_inj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:34:54.180802+00:00
-- url     : https://prove2.me/theorems/4f290a4a-8cd5-5642-a214-ef66b923cdf3
-- title:
--   W: ie inj
-- statement:
--   The W construction uses the ie inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L91-L96

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

theorem PI.VolNzeroOne.W.ie_inj {r : ℕ} {a b : Fin r}
    (h : (Fin.castAdd r (Fin.castSucc a) : Fin (r + 1 + r)) = Fin.castAdd r (Fin.castSucc b)) :
    a = b := by sorry
