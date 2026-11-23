-- Prove2me | Theorems.Thm_PI_NglqJacSplitW_chiM_mul
-- name    : PI.NglqJacSplitW.chiM_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:22.367795+00:00
-- url     : https://prove2.me/theorems/a4edbc8e-27cb-423c-abb3-e0938276c88b
-- title:
--   Nglq Jac Split W: chi M mul
-- statement:
--   The Nglq Jac Split W construction uses the chi M mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L51-L58

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

theorem PI.NglqJacSplitW.chiM_mul (A B : Matrix ι ι F) (hA : IsUnit A.det) (hB : IsUnit B.det)
    (hAB : IsUnit (A * B).det) : chiM (A * B) hAB = chiM A hA * chiM B hB := by sorry
