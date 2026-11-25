-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_gw_decomp
-- name    : PI.ScPiBuildW.Loc.LocFrame.gw_decomp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:55:51.184079+00:00
-- url     : https://prove2.me/theorems/e6931503-3cb4-4e99-b975-1f4e19a5aabb
-- title:
--   Loc Frame: gw decomp
-- statement:
--   The Loc Frame construction uses the gw decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L290-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L290-L292

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

theorem PI.ScPiBuildW.Loc.LocFrame.gw_decomp {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g) (b : Fin k) :
    g *ᵥ L.w b = ∑ c, L.M g c b • L.w c + ∑ a, hJ ε (L.f a) (g *ᵥ L.w b) • L.e a := by sorry
