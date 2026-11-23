-- Prove2me | Theorems.Thm_PI_PoincareSeriesInner_W_split
-- name    : PI.PoincareSeriesInner.W.split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:44.005391+00:00
-- url     : https://prove2.me/theorems/258591e3-8e78-4089-a727-ca09dd58d19e
-- title:
--   W: split
-- statement:
--   The W construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ComplexDoubleCosets/ComplexDoubleCoset.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ComplexDoubleCosets/ComplexDoubleCoset.lean#L36-L39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_CplxDC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldDCUnfold
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_ComplexDoubleCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
open PI PI.PoincareSeriesInner PI.PoincareSeriesInner.W
universe u

theorem PI.PoincareSeriesInner.W.split (z : ℂ) : z = ∑ k, cf k * ((part k z).toReal : ℂ) := by sorry
