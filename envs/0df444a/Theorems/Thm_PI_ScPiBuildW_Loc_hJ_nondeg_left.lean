-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_hJ_nondeg_left
-- name    : PI.ScPiBuildW.Loc.hJ_nondeg_left
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:47:31.367466+00:00
-- url     : https://prove2.me/theorems/0e0a76d4-a0a6-5d92-9047-7f200bc50d4c
-- title:
--   Loc: h J nondeg left
-- statement:
--   The Loc construction uses the h J nondeg left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L71-L72

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
variable {n : ℕ} (ε : Fin n → Bool)

theorem PI.ScPiBuildW.Loc.hJ_nondeg_left (x : Fin n → ℂ) (h : ∀ y, hJ ε x y = 0) : x = 0 := by sorry
