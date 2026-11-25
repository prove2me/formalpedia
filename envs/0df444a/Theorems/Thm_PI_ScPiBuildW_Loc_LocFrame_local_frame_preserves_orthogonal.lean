-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_local_frame_preserves_orthogonal
-- name    : PI.ScPiBuildW.Loc.LocFrame.local_frame_preserves_orthogonal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:41:42.644942+00:00
-- url     : https://prove2.me/theorems/a1bd2f97-267d-527b-9b84-835a936b72cb
-- title:
--   Loc Frame: local frame preserves orthogonal
-- statement:
--   The Loc Frame construction uses the local frame preserves orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L276-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L276-L283

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

theorem PI.ScPiBuildW.Loc.LocFrame.local_frame_preserves_orthogonal {y : Fin n → ℂ} (hy : ∀ a, hJ ε (L.e a) y = 0) (hz : hJ ε L.z y = 0) :
    hJ ε L.z (g *ᵥ y) = 0 := by sorry
