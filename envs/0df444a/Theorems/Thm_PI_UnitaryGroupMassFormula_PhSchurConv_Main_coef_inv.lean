-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhSchurConv_Main_coef_inv
-- name    : PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:46.502455+00:00
-- url     : https://prove2.me/theorems/b6655596-e078-57ec-8925-3377cb6f687d
-- title:
--   Main: coef inv
-- statement:
--   The Main construction uses the coef inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurConvolution/MapMulApply.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurConvolution/MapMulApply.lean#L29-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhSchurConv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurConvolution_MapMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhSchurConv PI.UnitaryGroupMassFormula.PhSchurConv.Main
open PI.PhSchurConv

theorem PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_inv {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g : G) (w : H) :
    ⟪w, σ g⁻¹ w⟫_ℂ = star ⟪w, σ g w⟫_ℂ := by sorry
