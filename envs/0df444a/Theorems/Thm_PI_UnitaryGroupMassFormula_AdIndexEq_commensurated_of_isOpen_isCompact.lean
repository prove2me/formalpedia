-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_commensurated_of_isOpen_isCompact
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:47:17.721801+00:00
-- url     : https://prove2.me/theorems/931da486-d31d-5ad4-b584-5cf836cbd65e
-- title:
--   Ad Index Eq: commensurated of is Open is Compact
-- statement:
--   The Ad Index Eq construction uses the commensurated of is Open is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CommensuratedOfIsOpenIsCompact.lean#L11-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CommensuratedOfIsOpenIsCompact.lean#L11-L34

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) :
    Commensurated K := by sorry
