-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_map_phi_indep
-- name    : PI.UnitaryGroupMassFormula.CdHaarScale.Main.map_phi_indep
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:02.434547+00:00
-- url     : https://prove2.me/theorems/9ca6dfa5-f6f6-4711-9e7f-2c4e44b99be4
-- title:
--   Main: map phi indep
-- statement:
--   The Main construction uses the map phi indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarScaling/MapEqSelfOfIterate.lean#L201-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarScaling/MapEqSelfOfIterate.lean#L201-L221

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

theorem PI.UnitaryGroupMassFormula.CdHaarScale.Main.map_phi_indep {P Q n : ℕ} {ε : Fin n → Bool} (e e' : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (h1' : ∀ i, ε (e' (Sum.inl i)) = true) (h2' : ∀ j, ε (e' (Sum.inr j)) = false)
    (μ : Measure (Formalism.BasicNotions.UpqT P Q)) [μ.IsHaarMeasure] :
    μ.map (phi e' h1' h2') = μ.map (phi e h1 h2) := by sorry
