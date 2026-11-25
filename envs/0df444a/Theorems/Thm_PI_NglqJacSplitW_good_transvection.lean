-- Prove2me | Theorems.Thm_PI_NglqJacSplitW_good_transvection
-- name    : PI.NglqJacSplitW.good_transvection
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:43.871791+00:00
-- url     : https://prove2.me/theorems/89b81ec0-d645-4f23-92b4-44332a7ea51d
-- title:
--   Nglq Jac Split W: good transvection
-- statement:
--   The Nglq Jac Split W construction uses the good transvection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L164-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L164-L227

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

theorem PI.NglqJacSplitW.good_transvection (i j : ι) (hij : i ≠ j) (c : F) : Good (transvection i j c) := by sorry
