-- Prove2me | Theorems.Thm_PI_NglqJacSplitW_chiM_diagOne
-- name    : PI.NglqJacSplitW.chiM_diagOne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:35.544734+00:00
-- url     : https://prove2.me/theorems/169d3749-1e36-4bb6-a834-8f911525bff0
-- title:
--   Nglq Jac Split W: chi M diag One
-- statement:
--   The Nglq Jac Split W construction uses the chi M diag One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L82-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L82-L98

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

theorem PI.NglqJacSplitW.chiM_diagOne (hD : DiagOne) (i : ι) (a : F) (ha : a ≠ 0)
    (h : IsUnit (diagonal (Function.update (1 : ι → F) i a)).det) :
    (chiM (diagonal (Function.update (1 : ι → F) i a)) h : ℝ≥0∞) = modF F a := by sorry
