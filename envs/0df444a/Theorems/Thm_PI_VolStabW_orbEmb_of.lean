-- Prove2me | Theorems.Thm_PI_VolStabW_orbEmb_of
-- name    : PI.VolStabW.orbEmb_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:55:48.822963+00:00
-- url     : https://prove2.me/theorems/945cf22a-e4e3-4128-994e-18cae62ab4e4
-- title:
--   Vol Stab W: orb Emb of
-- statement:
--   The Vol Stab W construction uses the orb Emb of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExStabTop.lean#L77-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExStabTop.lean#L77-L91

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

theorem PI.VolStabW.orbEmb_of (hW : SecCtblW) (hP : LCSCPolish) : OrbEmb := by sorry
