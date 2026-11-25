-- Prove2me | Theorems.Thm_PI_NglqJacSplitW_transvection_conj
-- name    : PI.NglqJacSplitW.transvection_conj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:46.822896+00:00
-- url     : https://prove2.me/theorems/6bed8a0f-18c4-4544-857f-a55b9b8cabe6
-- title:
--   Nglq Jac Split W: transvection conj
-- statement:
--   The Nglq Jac Split W construction uses the transvection conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L155-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L155-L162

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

theorem PI.NglqJacSplitW.transvection_conj {i j : ι} (hij : i ≠ j) {c : F} (hc : c ≠ 0) :
    transvection i j c = diagonal (Function.update (1 : ι → F) i c) * transvection i j 1 *
      diagonal (Function.update (1 : ι → F) i c⁻¹) := by sorry
