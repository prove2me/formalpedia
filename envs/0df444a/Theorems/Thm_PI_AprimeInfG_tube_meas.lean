-- Prove2me | Theorems.Thm_PI_AprimeInfG_tube_meas
-- name    : PI.AprimeInfG.tube_meas
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:18.523514+00:00
-- url     : https://prove2.me/theorems/0b5377fc-f1b1-5755-b241-baed9fe9a323
-- title:
--   Aprime Inf G: tube meas
-- statement:
--   The Aprime Inf G construction uses the tube meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpTube.lean#L40-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpTube.lean#L40-L90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Topology Filter Metric Set
open scoped ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.AprimeInfG.tube_meas (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) {V : Set G}
    (hV : ∀ a ∈ V, ∀ b ∈ V, a⁻¹ * b ∈ H → a = b) {S : Set H} (hS : MeasurableSet S)
    (hT : MeasurableSet (tubeS H V S)) (hVH : MeasurableSet (tubeS H V univ)) :
    ν univ * μ (tubeS H V S) = ν S * μ (tubeS H V univ) := by sorry
