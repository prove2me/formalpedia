-- Prove2me | Theorems.Thm_PI_VolStabSW_TopoAF_afTop_holds
-- name    : PI.VolStabSW.TopoAF.afTop_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:35:18.421536+00:00
-- url     : https://prove2.me/theorems/748591ba-6116-4ba3-b9c5-a464db9cae18
-- title:
--   Topo AF: af Top holds
-- statement:
--   The Topo AF construction uses the af Top holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/TopoAFTop.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/TopoAFTop.lean#L8-L9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TensTopOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAFTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.VolStabSW PI.VolStabSW.TopoAF

theorem PI.VolStabSW.TopoAF.afTop_holds : PI.VolSemiDirect.W.Lc.AFTop := by sorry
