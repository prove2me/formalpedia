-- Prove2me | Theorems.Thm_QPK_map_mul_right_eq_self
-- name    : QPK.map_mul_right_eq_self
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:15.500904+00:00
-- url     : https://prove2.me/theorems/ad57c8c4-f886-4fc2-80e0-9f02636c615e
-- title:
--   QPK: map mul right eq self
-- statement:
--   The QPK construction uses the map mul right eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/SiegelMeasureDefinition.lean#L88-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/SiegelMeasureDefinition.lean#L88-L127

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

theorem QPK.map_mul_right_eq_self (K : Set G) (hc : IsClosed K) (hK : IsGrp K) (μ : Measure G)
    (hμ : InvOn μ K) (hfin : μ K ≠ ⊤) (s : G) (hs : s ∈ K) :
    μ.map (fun x => x * s) = μ := by sorry
