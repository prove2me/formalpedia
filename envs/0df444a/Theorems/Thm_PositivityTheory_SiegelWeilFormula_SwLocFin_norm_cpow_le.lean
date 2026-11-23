-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_SwLocFin_norm_cpow_le
-- name    : PositivityTheory.SiegelWeilFormula.SwLocFin.norm_cpow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:00.299307+00:00
-- url     : https://prove2.me/theorems/fe83fbd5-b183-4bea-b221-d9156978566f
-- title:
--   Sw Loc Fin: norm cpow le
-- statement:
--   The Sw Loc Fin construction uses the norm cpow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalCharacterIntegrals/DifferentiableSetIntegralFz.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalCharacterIntegrals/DifferentiableSetIntegralFz.lean#L13-L17

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

theorem PositivityTheory.SiegelWeilFormula.SwLocFin.norm_cpow_le {x : ℝ} (hx : 1 ≤ x) {R : ℝ} (hR : x ≤ R) (w : ℂ) :
    ‖(x : ℂ) ^ w‖ ≤ R ^ max w.re 0 := by sorry
