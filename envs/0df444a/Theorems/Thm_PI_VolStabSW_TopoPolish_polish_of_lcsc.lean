-- Prove2me | Theorems.Thm_PI_VolStabSW_TopoPolish_polish_of_lcsc
-- name    : PI.VolStabSW.TopoPolish.polish_of_lcsc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:41:42.993346+00:00
-- url     : https://prove2.me/theorems/7aa11c94-c7a9-433c-804f-9e81ab1c5798
-- title:
--   Topo Polish: polish of lcsc
-- statement:
--   The Topo Polish construction uses the polish of lcsc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/TopoPolish.lean#L9-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/TopoPolish.lean#L9-L39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoPolish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.TopoPolish
open Topology TopologicalSpace Set

theorem PI.VolStabSW.TopoPolish.polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by sorry
