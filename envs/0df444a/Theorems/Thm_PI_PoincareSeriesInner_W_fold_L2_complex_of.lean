-- Prove2me | Theorems.Thm_PI_PoincareSeriesInner_W_fold_L2_complex_of
-- name    : PI.PoincareSeriesInner.W.fold_L2_complex_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:54.225857+00:00
-- url     : https://prove2.me/theorems/e6518c30-3dcc-46f5-bb41-978a7dd7b7fe
-- title:
--   W: fold L2 complex of
-- statement:
--   The W construction uses the fold L2 complex of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ComplexDoubleCosets/FoldL2ComplexOf.lean#L16-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ComplexDoubleCosets/FoldL2ComplexOf.lean#L16-L95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_CplxDC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldDCUnfold
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldUnfold
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_TranslationIndependent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_FoldL2ComplexOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
open PI PI.PoincareSeriesInner PI.PoincareSeriesInner.W
universe u

theorem PI.PoincareSeriesInner.W.fold_L2_complex_of (hc : CplxDC.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : PoincareSeriesInner G μ := by sorry
