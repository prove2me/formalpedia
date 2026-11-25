-- Prove2me | Theorems.Thm_P2M_PI_VolStabW_map_smulSub__e7a25be11816
-- name    : P2M_PI_VolStabW_map_smulSub__e7a25be11816
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:04:52.841993+00:00
-- url     : https://prove2.me/theorems/16a22e4b-e392-433a-b703-205636082677
-- title:
--   P2 M PI Vol Stab W map smul Sub  e7a25be11816: P2 M PI Vol Stab W map smul Sub  e7a25be11816
-- statement:
--   The P2 M PI Vol Stab W map smul Sub  e7a25be11816 construction uses the P2 M PI Vol Stab W map smul Sub  e7a25be11816 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHH.lean#L182-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHH.lean#L182-L193

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix

theorem P2M_PI_VolStabW_map_smulSub__e7a25be11816 {K V X : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup X]
    [Module K X] (D : V →+ X) (hDs : ∀ (t : K) w, D (t • w) = t • D w) (t : K)
    (L : AddSubgroup V) : (smulSub t L).map D = smulSub t (L.map D) := by sorry

alias «PI».«VolStabW».«map_smulSub'» := P2M_PI_VolStabW_map_smulSub__e7a25be11816
