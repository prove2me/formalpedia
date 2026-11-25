-- Prove2me | Theorems.Thm_PI_VolStabSW_nuFin_holds
-- name    : PI.VolStabSW.nuFin_holds
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:45:40.928813+00:00
-- url     : https://prove2.me/theorems/285981eb-f9da-504d-ab1f-e703d10bf660
-- title:
--   Vol Stab SW: nu Fin holds
-- statement:
--   The Vol Stab SW construction uses the nu Fin holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/TopoNuFin.lean#L159-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/TopoNuFin.lean#L159-L162

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoNuFin
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Filter Topology
  PI.VolFromSW PI.VolStabSW.PositiveNearLattice PI.VolStabSW.TopoNuFin
open scoped TensorProduct ENNReal

theorem PI.VolStabSW.nuFin_holds : NuFin := by sorry
