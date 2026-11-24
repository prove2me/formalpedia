-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_wf
-- name    : PI.ScPiBuildW.Loc.LocFrame.wf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:54:12.185001+00:00
-- url     : https://prove2.me/theorems/25b4aa9b-804f-44c5-b67e-1ae3d42898de
-- title:
--   Loc Frame: wf
-- statement:
--   The Loc Frame construction uses the wf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L125-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L125-L126

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

theorem PI.ScPiBuildW.Loc.LocFrame.wf (c : Fin k) (a : Fin r) : hJ ε (L.w c) (L.f a) = 0 := by sorry
