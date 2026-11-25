-- Prove2me | Theorems.Thm_PI_AprimeInfG_contAt_dens
-- name    : PI.AprimeInfG.contAt_dens
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:22.588882+00:00
-- url     : https://prove2.me/theorems/15fd6a7f-5300-5480-b116-ab5a12bd6f16
-- title:
--   Aprime Inf G: cont At dens
-- statement:
--   The Aprime Inf G construction uses the cont At dens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpChartC.lean#L123-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpChartC.lean#L123-L126

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpChartC
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

theorem PI.AprimeInfG.contAt_dens {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {F : P → P} {F' : P → (P →L[ℝ] P)}
    {D : P → ℝ} (hF : ContinuousAt F 0) (hdet : ContinuousAt (fun p => |(F' p).det|) 0) (hD : ContinuousAt D (F 0)) :
    ContinuousAt (fun p => |(F' p).det| * D (F p)) 0 := by sorry
