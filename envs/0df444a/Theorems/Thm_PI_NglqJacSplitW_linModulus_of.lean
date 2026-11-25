-- Prove2me | Theorems.Thm_PI_NglqJacSplitW_linModulus_of
-- name    : PI.NglqJacSplitW.linModulus_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:38.643012+00:00
-- url     : https://prove2.me/theorems/53b1399b-26bf-4e11-b8cd-3a4fcd830db6
-- title:
--   Nglq Jac Split W: lin Modulus of
-- statement:
--   The Nglq Jac Split W construction uses the lin Modulus of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L229-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L229-L237

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

theorem PI.NglqJacSplitW.linModulus_of (hD : DiagOne) : LinModulus := by sorry
