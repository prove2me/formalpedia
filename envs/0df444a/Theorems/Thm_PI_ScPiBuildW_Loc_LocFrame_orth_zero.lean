-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_orth_zero
-- name    : PI.ScPiBuildW.Loc.LocFrame.orth_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:37:36.220212+00:00
-- url     : https://prove2.me/theorems/0fbf580b-a6f5-4509-ab2f-4aa85a80faae
-- title:
--   Loc Frame: orth zero
-- statement:
--   The Loc Frame construction uses the orth zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L179-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L179-L191

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.ScPiBuildW PI.ScPiBuildW.Loc
open PI.ScPiExists
open PI.ScPiBuildW.Loc.LocFrame
variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)

theorem PI.ScPiBuildW.Loc.LocFrame.orth_zero (y : Fin n → ℂ) (he : ∀ a, hJ ε (L.e a) y = 0) (hf : ∀ a, hJ ε (L.f a) y = 0)
    (hz : hJ ε L.z y = 0) (hw : ∀ c, hJ ε (L.w c) y = 0) : y = 0 := by sorry
