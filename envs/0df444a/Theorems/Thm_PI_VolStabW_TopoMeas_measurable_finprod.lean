-- Prove2me | Theorems.Thm_PI_VolStabW_TopoMeas_measurable_finprod
-- name    : PI.VolStabW.TopoMeas.measurable_finprod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:50:43.673152+00:00
-- url     : https://prove2.me/theorems/691a79ff-314a-59c7-9631-3e014a9e41a4
-- title:
--   Topo Meas: measurable finprod
-- statement:
--   The Topo Meas construction uses the measurable finprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TopoMeas.lean#L13-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TopoMeas.lean#L13-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasOrbSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.TopoMeas
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Filter Topology PI.VolFromSW
open scoped TensorProduct

theorem PI.VolStabW.TopoMeas.measurable_finprod {X ι : Type} [MeasurableSpace X] [Countable ι] (f : ι → X → ℂ)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x => ∏ᶠ i, f i x) := by sorry
