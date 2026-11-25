-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_map_conj_of_mem_normalizer
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.map_conj_of_mem_normalizer
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:47:51.050105+00:00
-- url     : https://prove2.me/theorems/5b0ce037-4731-524c-99e5-3bf8a637ad0b
-- title:
--   Ad Index Eq: map conj of mem normalizer
-- statement:
--   The Ad Index Eq construction uses the map conj of mem normalizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ModQEqOneOfMemNormalizer.lean#L140-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ModQEqOneOfMemNormalizer.lean#L140-L154

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
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
variable {G : Type} [Group G]

theorem PI.UnitaryGroupMassFormula.AdIndexEq.map_conj_of_mem_normalizer (K : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    K.map (MulAut.conj x).toMonoidHom = K := by sorry
