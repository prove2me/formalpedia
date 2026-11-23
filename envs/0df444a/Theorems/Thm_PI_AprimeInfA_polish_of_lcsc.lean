-- Prove2me | Theorems.Thm_PI_AprimeInfA_polish_of_lcsc
-- name    : PI.AprimeInfA.polish_of_lcsc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:36.443086+00:00
-- url     : https://prove2.me/theorems/96708eb8-04c1-4cf2-88cf-a90e183e7ee5
-- title:
--   Aprime Inf A: polish of lcsc
-- statement:
--   The Aprime Inf A construction uses the polish of lcsc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/LintegralMulRightOfMem.lean#L10-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/LintegralMulRightOfMem.lean#L10-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfA
open MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal NNReal

theorem PI.AprimeInfA.polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by sorry
