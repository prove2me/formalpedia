-- Prove2me | Theorems.Thm_PI_NglqJacSplitW_chiM_spec
-- name    : PI.NglqJacSplitW.chiM_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:58.943079+00:00
-- url     : https://prove2.me/theorems/1ad6160f-5cbc-42c1-acac-e9c7faacd463
-- title:
--   Nglq Jac Split W: chi M spec
-- statement:
--   The Nglq Jac Split W construction uses the chi M spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L29-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean#L29-L49

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

theorem PI.NglqJacSplitW.chiM_spec [mF : MeasurableSpace (ι → F)] [hB : BorelSpace (ι → F)] (M : Matrix ι ι F)
    (hM : IsUnit M.det) (ν : Measure (ι → F)) [ν.IsAddHaarMeasure] (S : Set (ι → F)) :
    ν ((fun x => M *ᵥ x) '' S) = chiM M hM * ν S := by sorry
