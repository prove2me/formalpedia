-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_hJ_span_left
-- name    : PI.ScPiBuildW.Loc.hJ_span_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:56:09.662452+00:00
-- url     : https://prove2.me/theorems/da3e27bc-0a60-4220-a2e8-b95ba62a5a3d
-- title:
--   Loc: h J span left
-- statement:
--   The Loc construction uses the h J span left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L80-L86

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

theorem PI.ScPiBuildW.Loc.hJ_span_left {S : Set (Fin n → ℂ)} {x y : Fin n → ℂ} (hx : x ∈ Submodule.span ℂ S)
    (h : ∀ a ∈ S, hJ ε a y = 0) : hJ ε x y = 0 := by sorry
