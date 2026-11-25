-- Prove2me | Theorems.Thm_PI_NglqJacSplitW_good_mul
-- name    : PI.NglqJacSplitW.good_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:05.953317+00:00
-- url     : https://prove2.me/theorems/eb007d0e-9bd2-4d16-9768-abaf4c43ee88
-- title:
--   Nglq Jac Split W: good mul
-- statement:
--   The Nglq Jac Split W construction uses the good mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L103-L107

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

theorem PI.NglqJacSplitW.good_mul {A B : Matrix ι ι F} (hA0 : A.det ≠ 0) (hB0 : B.det ≠ 0)
    (hA : Good A) (hB : Good B) : Good (A * B) := by sorry
