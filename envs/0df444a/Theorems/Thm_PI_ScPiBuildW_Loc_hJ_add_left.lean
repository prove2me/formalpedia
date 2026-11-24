-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_hJ_add_left
-- name    : PI.ScPiBuildW.Loc.hJ_add_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:54:27.708307+00:00
-- url     : https://prove2.me/theorems/b414eb59-0899-40f2-af37-5d763d019b82
-- title:
--   Loc: h J add left
-- statement:
--   The Loc construction uses the h J add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L17-L18

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

theorem PI.ScPiBuildW.Loc.hJ_add_left (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by sorry
