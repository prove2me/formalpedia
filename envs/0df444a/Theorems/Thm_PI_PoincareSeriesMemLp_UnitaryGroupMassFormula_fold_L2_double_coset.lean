-- Prove2me | Theorems.Thm_PI_PoincareSeriesMemLp_UnitaryGroupMassFormula_fold_L2_double_coset
-- name    : PI.PoincareSeriesMemLp.UnitaryGroupMassFormula.fold_L2_double_coset
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:36:21.278017+00:00
-- url     : https://prove2.me/theorems/4bf6fc1c-efff-4a4d-b8f8-9bbb138ba4a5
-- title:
--   Unitary Group Mass Formula: fold L2 double coset
-- statement:
--   The Unitary Group Mass Formula construction uses the fold L2 double coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PoincareSeriesMeasurability/FoldL2DoubleCoset.lean#L34-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PoincareSeriesMeasurability/FoldL2DoubleCoset.lean#L34-L106

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldUnfold
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoincareSeriesMeasurability_FoldL2DoubleCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open PI PI.PoincareSeriesMemLp PI.PoincareSeriesMemLp.UnitaryGroupMassFormula
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

theorem PI.PoincareSeriesMemLp.UnitaryGroupMassFormula.fold_L2_double_coset (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : PoincareSeriesMemLp G μ := by sorry
