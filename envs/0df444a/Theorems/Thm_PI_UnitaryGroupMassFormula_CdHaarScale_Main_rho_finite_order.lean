-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_rho_finite_order
-- name    : PI.UnitaryGroupMassFormula.CdHaarScale.Main.rho_finite_order
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:16.902517+00:00
-- url     : https://prove2.me/theorems/021d638b-c555-4fd8-9ec8-99d8f08b450f
-- title:
--   Main: rho finite order
-- statement:
--   The Main construction uses the rho finite order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarScaling/MapEqSelfOfIterate.lean#L128-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarScaling/MapEqSelfOfIterate.lean#L128-L137

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CdHaarScale PI.UnitaryGroupMassFormula.CdHaarScale.Main

theorem PI.UnitaryGroupMassFormula.CdHaarScale.Main.rho_finite_order {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ a, (rho π hπ)^[N] a = a := by sorry
