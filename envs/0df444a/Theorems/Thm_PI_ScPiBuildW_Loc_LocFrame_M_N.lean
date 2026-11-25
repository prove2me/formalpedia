-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_M_N
-- name    : PI.ScPiBuildW.Loc.LocFrame.M_N
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:37:18.367996+00:00
-- url     : https://prove2.me/theorems/8836b610-208e-4b6b-b073-a1fcf3b2d1c1
-- title:
--   Loc Frame: M N
-- statement:
--   The Loc Frame construction uses the M N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L335-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L335-L342

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

theorem PI.ScPiBuildW.Loc.LocFrame.M_N {g : Matrix (Fin n) (Fin n) ℂ} (hN : InN ε L.e L.z g) : L.M g = 1 := by sorry
