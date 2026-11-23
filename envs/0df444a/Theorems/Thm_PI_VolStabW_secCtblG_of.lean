-- Prove2me | Theorems.Thm_PI_VolStabW_secCtblG_of
-- name    : PI.VolStabW.secCtblG_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:57.351841+00:00
-- url     : https://prove2.me/theorems/1d2086ab-a428-4573-affd-cf5b89e829fa
-- title:
--   Vol Stab W: sec Ctbl G of
-- statement:
--   The Vol Stab W construction uses the sec Ctbl G of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExStabTop.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExStabTop.lean#L63-L75

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabTop
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

theorem PI.VolStabW.secCtblG_of (hW : SecCtblW) : SecCtblG := by sorry
