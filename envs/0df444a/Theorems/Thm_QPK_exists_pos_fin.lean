-- Prove2me | Theorems.Thm_QPK_exists_pos_fin
-- name    : QPK.exists_pos_fin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:31.773299+00:00
-- url     : https://prove2.me/theorems/dfe6937b-e60a-46e7-a371-9aabc9a8f78d
-- title:
--   QPK: exists pos fin
-- statement:
--   The QPK construction uses the exists pos fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/SiegelMeasureDefinition.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/SiegelMeasureDefinition.lean#L30-L39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_SiegelMeasureDefinition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology Set
open scoped ENNReal Pointwise
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem QPK.exists_pos_fin (μ : Measure G) [SigmaFinite μ] (h0 : μ ≠ 0) :
    ∃ A : Set G, μ A ≠ 0 ∧ μ A ≠ ⊤ := by sorry
