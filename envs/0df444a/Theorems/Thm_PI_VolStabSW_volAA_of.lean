-- Prove2me | Theorems.Thm_PI_VolStabSW_volAA_of
-- name    : PI.VolStabSW.volAA_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:39:36.09158+00:00
-- url     : https://prove2.me/theorems/4d7526e2-eafa-5700-9982-fb1937d68ea6
-- title:
--   Vol Stab SW: vol AA of
-- statement:
--   The Vol Stab SW construction uses the vol AA of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensVol.lean#L12-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensVol.lean#L12-L27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVol
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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW PositiveNearLattice SdDualW VolAAW

theorem PI.VolStabSW.volAA_of (hC : CondAA) : VolAA := by sorry
