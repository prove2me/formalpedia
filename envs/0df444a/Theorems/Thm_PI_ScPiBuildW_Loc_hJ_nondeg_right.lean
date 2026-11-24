-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_hJ_nondeg_right
-- name    : PI.ScPiBuildW.Loc.hJ_nondeg_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:54:34.674805+00:00
-- url     : https://prove2.me/theorems/a1fe0a42-29ee-40fa-b992-b991605c9c52
-- title:
--   Loc: h J nondeg right
-- statement:
--   The Loc construction uses the h J nondeg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L53-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L53-L69

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

theorem PI.ScPiBuildW.Loc.hJ_nondeg_right (y : Fin n → ℂ) (h : ∀ x, hJ ε x y = 0) : y = 0 := by sorry
