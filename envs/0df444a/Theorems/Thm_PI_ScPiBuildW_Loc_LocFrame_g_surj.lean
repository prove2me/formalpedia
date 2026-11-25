-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_g_surj
-- name    : PI.ScPiBuildW.Loc.LocFrame.g_surj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:37:41.871941+00:00
-- url     : https://prove2.me/theorems/42d45359-53d7-4a10-b43f-935edb25aa42
-- title:
--   Loc Frame: g surj
-- statement:
--   The Loc Frame construction uses the g surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L260-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L260-L269

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
variable {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g)
include hg hS

theorem PI.ScPiBuildW.Loc.LocFrame.g_surj {x : Fin n → ℂ} (hx : x ∈ L.X) : ∃ x' ∈ L.X, g *ᵥ x' = x := by sorry
