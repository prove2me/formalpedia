-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_ksub_isOpen
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.ksub_isOpen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:39:48.834354+00:00
-- url     : https://prove2.me/theorems/045d862d-cd17-42b1-b51f-598d96cb75e4
-- title:
--   Ad Index Eq: ksub is Open
-- statement:
--   The Ad Index Eq construction uses the ksub is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CommensuratedOfIsOpenIsCompact.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CommensuratedOfIsOpenIsCompact.lean#L36-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CommensuratedOfIsOpenIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open Formalism.MainNotions.S

theorem PI.UnitaryGroupMassFormula.AdIndexEq.ksub_isOpen (I : AutInst) : IsOpen ((PI.AdIndexEq.Ksub I : Subgroup I.Gf) : Set I.Gf) := by sorry
