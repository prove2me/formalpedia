-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_g_perp
-- name    : PI.ScPiBuildW.Loc.LocFrame.g_perp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:54:20.338452+00:00
-- url     : https://prove2.me/theorems/9491c8b1-6c32-4b16-b797-6f26837847e6
-- title:
--   Loc Frame: g perp
-- statement:
--   The Loc Frame construction uses the g perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L271-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L271-L274

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

theorem PI.ScPiBuildW.Loc.LocFrame.g_perp {y : Fin n → ℂ} (hy : ∀ a, hJ ε (L.e a) y = 0) (a : Fin r) : hJ ε (L.e a) (g *ᵥ y) = 0 := by sorry
