-- Prove2me | Theorems.Thm_PI_VolStabSW_cos_inter_eq
-- name    : PI.VolStabSW.cos_inter_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:38:43.771987+00:00
-- url     : https://prove2.me/theorems/115bb158-eb91-49aa-b363-152e6a60f0b2
-- title:
--   Vol Stab SW: cos inter eq
-- statement:
--   The Vol Stab SW construction uses the cos inter eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensHF.lean#L210-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensHF.lean#L210-L213

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HenselCountHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]

theorem PI.VolStabSW.cos_inter_eq (Λ0 : AddSubgroup V) (Hn : AddSubgroup X) (G : V → X) (y : V) (T : X) :
    {x | x - y ∈ Λ0} ∩ G ⁻¹' {z | z - T ∈ Hn} = (fun x => -y + x) ⁻¹' hlev Λ0 Hn G y T := by sorry
