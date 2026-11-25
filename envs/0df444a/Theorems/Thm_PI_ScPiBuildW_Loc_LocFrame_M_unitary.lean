-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_M_unitary
-- name    : PI.ScPiBuildW.Loc.LocFrame.M_unitary
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:37:49.896114+00:00
-- url     : https://prove2.me/theorems/4e53f615-d44a-4fcc-b83b-59614975d96b
-- title:
--   Loc Frame: M unitary
-- statement:
--   The Loc Frame construction uses the M unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L323-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L323-L333

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

theorem PI.ScPiBuildW.Loc.LocFrame.M_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g) :
    (L.M g)ᴴ * L.M g = 1 := by sorry
