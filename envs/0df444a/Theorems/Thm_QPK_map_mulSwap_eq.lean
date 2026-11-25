-- Prove2me | Theorems.Thm_QPK_map_mulSwap_eq
-- name    : QPK.map_mulSwap_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:31.313805+00:00
-- url     : https://prove2.me/theorems/e78ee097-a757-442a-abe3-399abc1fd939
-- title:
--   QPK: map mul Swap eq
-- statement:
--   The QPK construction uses the map mul Swap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/SiegelMeasureDefinition.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/SiegelMeasureDefinition.lean#L129-L135

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

theorem QPK.map_mulSwap_eq (Q : Measure (G × G)) (g : G × G → G × G) (hg : MeasurePreserving g Q Q)
    (f : G → G) (hf : Measurable f) (h : ∀ p : G × G, f (p.2 * p.1) = (g p).2 * (g p).1) :
    (Q.map (fun p : G × G => p.2 * p.1)).map f = Q.map (fun p : G × G => p.2 * p.1) := by sorry
