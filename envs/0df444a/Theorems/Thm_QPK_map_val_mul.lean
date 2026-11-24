-- Prove2me | Theorems.Thm_QPK_map_val_mul
-- name    : QPK.map_val_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:41.948707+00:00
-- url     : https://prove2.me/theorems/e10ec002-b105-4036-8a4d-3ade19256884
-- title:
--   QPK: map val mul
-- statement:
--   The QPK construction uses the map val mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/HaarMeasureUniqueness.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/HaarMeasureUniqueness.lean#L22-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem QPK.map_val_mul (K' : Subgroup G) (g : K') (α : Measure K') :
    (α.map (fun x => g * x)).map Subtype.val = (α.map Subtype.val).map (fun x => (g : G) * x) := by sorry
