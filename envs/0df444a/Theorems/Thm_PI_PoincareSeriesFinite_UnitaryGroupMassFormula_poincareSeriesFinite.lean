-- Prove2me | Theorems.Thm_PI_PoincareSeriesFinite_UnitaryGroupMassFormula_poincareSeriesFinite
-- name    : PI.PoincareSeriesFinite.UnitaryGroupMassFormula.poincareSeriesFinite
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:36:11.563584+00:00
-- url     : https://prove2.me/theorems/b6764c1c-99fc-488a-8a6b-2bf66ca9b55e
-- title:
--   Unitary Group Mass Formula: poincare Series Finite
-- statement:
--   The Unitary Group Mass Formula construction uses the poincare Series Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientIntegralBound/QuotientLIntegralLeMultiplicityLIntegral.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientIntegralBound/QuotientLIntegralLeMultiplicityLIntegral.lean#L26-L35

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientIntegralBound_QuotientLIntegralLeMultiplicityLIntegral
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
open scoped ENNReal NNReal
open PI PI.PoincareSeriesFinite PI.PoincareSeriesFinite.UnitaryGroupMassFormula
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

theorem PI.PoincareSeriesFinite.UnitaryGroupMassFormula.poincareSeriesFinite (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : PoincareSeriesFinite G μ := by sorry
