-- Prove2me | Theorems.Thm_PI_AprimeInfG_mem_tubeS_mul_iff
-- name    : PI.AprimeInfG.mem_tubeS_mul_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:47.861188+00:00
-- url     : https://prove2.me/theorems/b51fd240-b44f-4753-8b0d-5abceafd909e
-- title:
--   Aprime Inf G: mem tube S mul iff
-- statement:
--   The Aprime Inf G construction uses the mem tube S mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpTube.lean#L18-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpTube.lean#L18-L38

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

theorem PI.AprimeInfG.mem_tubeS_mul_iff (H : Subgroup G) {V : Set G} (hV : ∀ a ∈ V, ∀ b ∈ V, a⁻¹ * b ∈ H → a = b)
    (S : Set H) {a : G} (ha : a ∈ V) (h0 h : H) :
    a * (h0 : G) * (h : G) ∈ tubeS H V S ↔ h0 * h ∈ S := by sorry
