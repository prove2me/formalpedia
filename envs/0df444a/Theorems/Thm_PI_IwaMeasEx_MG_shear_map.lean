-- Prove2me | Theorems.Thm_PI_IwaMeasEx_MG_shear_map
-- name    : PI.IwaMeasEx.MG.shear_map
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:45.655491+00:00
-- url     : https://prove2.me/theorems/c9e0b178-2152-45c8-9462-558f43a83409
-- title:
--   MG: shear map
-- statement:
--   The MG construction uses the shear map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IwasawaMeasureExistence/MulEquivHaarCharEqOfChart.lean#L47-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IwasawaMeasureExistence/MulEquivHaarCharEqOfChart.lean#L47-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IwasawaMeasureExistence_MulEquivHaarCharEqOfChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IwaMeasEx PI.IwaMeasEx.MG
open MeasureTheory Measure Topology Set
open scoped ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
variable {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [IsTopologicalAddGroup Y] [LocallyCompactSpace Y]

theorem PI.IwaMeasEx.MG.shear_map {A B : Type*} [MeasurableSpace A] [AddGroup B] [MeasurableSpace B] [MeasurableAdd₂ B]
    [MeasurableAdd B] (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [ν.IsAddRightInvariant]
    (f : A → B) (hf : Measurable f) :
    (μ.prod ν).map (fun p : A × B => (p.1, p.2 + f p.1)) = μ.prod ν := by sorry
