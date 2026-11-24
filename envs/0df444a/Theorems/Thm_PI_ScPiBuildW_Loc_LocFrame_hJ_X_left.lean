-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_hJ_X_left
-- name    : PI.ScPiBuildW.Loc.LocFrame.hJ_X_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:56:47.197267+00:00
-- url     : https://prove2.me/theorems/35f6d5a2-0b24-4fd9-88c4-76bf57d8d523
-- title:
--   Loc Frame: h J X left
-- statement:
--   The Loc Frame construction uses the h J X left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L221-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L221-L222

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

theorem PI.ScPiBuildW.Loc.LocFrame.hJ_X_left {x y : Fin n → ℂ} (hx : x ∈ L.X) (h : ∀ a, hJ ε (L.e a) y = 0) : hJ ε x y = 0 := by sorry
