-- Prove2me | Theorems.Thm_PI_WeilQuotMeas_UnitaryGroupMassFormula_exists_compact_lift
-- name    : PI.WeilQuotMeas.UnitaryGroupMassFormula.exists_compact_lift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:56.513254+00:00
-- url     : https://prove2.me/theorems/dc9e9e15-916e-456d-9e9c-9862bf702a71
-- title:
--   Unitary Group Mass Formula: exists compact lift
-- statement:
--   The Unitary Group Mass Formula construction uses the exists compact lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientMeasure/LintegralMulAvgComm.lean#L54-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientMeasure/LintegralMulAvgComm.lean#L54-L68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_StepBruhat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_LintegralMulAvgComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal Pointwise
open PI PI.WeilQuotMeas PI.WeilQuotMeas.UnitaryGroupMassFormula
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}

theorem PI.WeilQuotMeas.UnitaryGroupMassFormula.exists_compact_lift (K : Set (G ⧸ H)) (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ K ⊆ (QuotientGroup.mk : G → G ⧸ H) '' C := by sorry
