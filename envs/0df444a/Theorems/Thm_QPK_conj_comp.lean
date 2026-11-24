-- Prove2me | Theorems.Thm_QPK_conj_comp
-- name    : QPK.conj_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:14:23.10751+00:00
-- url     : https://prove2.me/theorems/3b27b316-a20f-44c4-a829-68143df583d9
-- title:
--   QPK: conj comp
-- statement:
--   The QPK construction uses the conj comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ConjugationInvariantMeasure.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ConjugationInvariantMeasure.lean#L33-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ConjugationInvariantMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem QPK.conj_comp (g h : G) :
    (fun x : G => g * x * g⁻¹) ∘ (fun x : G => h * x * h⁻¹) = fun x => (g * h) * x * (g * h)⁻¹ := by sorry
