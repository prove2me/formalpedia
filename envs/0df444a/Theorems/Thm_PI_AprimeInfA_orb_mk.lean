-- Prove2me | Theorems.Thm_PI_AprimeInfA_orb_mk
-- name    : PI.AprimeInfA.orb_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:25.23323+00:00
-- url     : https://prove2.me/theorems/a91ef373-a161-42a5-8811-a92872314bb2
-- title:
--   Aprime Inf A: orb mk
-- statement:
--   The Aprime Inf A construction uses the orb mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/LintegralMulRightOfMem.lean#L209-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/LintegralMulRightOfMem.lean#L209-L213

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
variable {X : Type} [MulAction G X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

theorem PI.AprimeInfA.orb_mk (x0 : X) (g : G) :
    ((g : G ⧸ MulAction.stabilizer G x0)).out • x0 = g • x0 := by sorry
