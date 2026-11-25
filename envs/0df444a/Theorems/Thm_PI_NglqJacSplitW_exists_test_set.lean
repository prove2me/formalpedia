-- Prove2me | Theorems.Thm_PI_NglqJacSplitW_exists_test_set
-- name    : PI.NglqJacSplitW.exists_test_set
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:34.301988+00:00
-- url     : https://prove2.me/theorems/d772af8f-76f6-5c35-b447-35858d07990e
-- title:
--   Nglq Jac Split W: exists test set
-- statement:
--   The Nglq Jac Split W construction uses the exists test set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L77-L80

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal
open PI PI.NglqJacSplitW
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PI.NglqJacSplitW.exists_test_set [MeasurableSpace (ι → F)] [BorelSpace (ι → F)] (ν : Measure (ι → F))
    [ν.IsAddHaarMeasure] : ∃ K : Set (ι → F), MeasurableSet K ∧ ν K ≠ 0 ∧ ν K ≠ ∞ := by sorry
