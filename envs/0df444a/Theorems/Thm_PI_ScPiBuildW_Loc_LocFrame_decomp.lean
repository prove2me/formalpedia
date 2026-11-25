-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_decomp
-- name    : PI.ScPiBuildW.Loc.LocFrame.decomp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:37:51.25823+00:00
-- url     : https://prove2.me/theorems/3eafe380-7265-4d7b-b437-502f0eee01e5
-- title:
--   Loc Frame: decomp
-- statement:
--   The Loc Frame construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L193-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L193-L208

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

theorem PI.ScPiBuildW.Loc.LocFrame.decomp (y : Fin n → ℂ) (he : ∀ a, hJ ε (L.e a) y = 0) (hz : hJ ε L.z y = 0) :
    y = ∑ c, hJ ε (L.w c) y • L.w c + ∑ a, hJ ε (L.f a) y • L.e a := by sorry
