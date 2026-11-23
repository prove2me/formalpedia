-- Prove2me | Theorems.Thm_PI_AprimeInfA_map_mul_right_eq
-- name    : PI.AprimeInfA.map_mul_right_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:31.632478+00:00
-- url     : https://prove2.me/theorems/6e6ac302-df82-4297-8a0d-a2e21a8dff07
-- title:
--   Aprime Inf A: map mul right eq
-- statement:
--   The Aprime Inf A construction uses the map mul right eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/LintegralMulRightOfMem.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/LintegralMulRightOfMem.lean#L47-L51

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.AprimeInfA.map_mul_right_eq (μ : Measure G) [μ.IsHaarMeasure] (g : G) :
    μ.map (· * g) = Measure.modularCharacterFun g • μ := by sorry
