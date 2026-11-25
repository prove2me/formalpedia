-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_SwLocFin_differentiable_setIntegral_fz
-- name    : PositivityTheory.SiegelWeilFormula.SwLocFin.differentiable_setIntegral_fz
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:03:41.173348+00:00
-- url     : https://prove2.me/theorems/443a6642-479d-5c37-87e8-e4dbd0ed0dfd
-- title:
--   Sw Loc Fin: differentiable set Integral fz
-- statement:
--   The Sw Loc Fin construction uses the differentiable set Integral fz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalCharacterIntegrals/DifferentiableSetIntegralFz.lean#L32-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalCharacterIntegrals/DifferentiableSetIntegralFz.lean#L32-L82

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalCharacterIntegrals_DifferentiableSetIntegralFz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.SwLocFin
open MeasureTheory Filter Topology Set
variable {H : Type*} [MeasurableSpace H]

theorem PositivityTheory.SiegelWeilFormula.SwLocFin.differentiable_setIntegral_fz {ν : Measure H} {r : H → ℝ} {u : H → ℂ} {s₀ : ℂ} (hr1 : ∀ b, 1 ≤ r b)
    (hrm : Measurable r) (hum : AEStronglyMeasurable u ν) {C : ℝ} (hub : ∀ b, ‖u b‖ ≤ C) {S : Set H}
    (hS : MeasurableSet S) (hSf : ν S < ⊤) {Rm : ℝ} (hRm : ∀ b ∈ S, r b ≤ Rm) :
    Differentiable ℂ (fun z => ∫ b in S, fz r u s₀ z b ∂ν) := by sorry
