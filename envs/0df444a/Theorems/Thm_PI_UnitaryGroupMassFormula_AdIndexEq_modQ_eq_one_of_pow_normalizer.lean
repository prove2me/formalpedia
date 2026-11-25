-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_eq_one_of_pow_normalizer
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.modQ_eq_one_of_pow_normalizer
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:54.053806+00:00
-- url     : https://prove2.me/theorems/53c32e2a-1e68-56d9-a251-39e30669b387
-- title:
--   Ad Index Eq: mod Q eq one of pow normalizer
-- statement:
--   The Ad Index Eq construction uses the mod Q eq one of pow normalizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ModQEqOneOfMemNormalizer.lean#L177-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ModQEqOneOfMemNormalizer.lean#L177-L179

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.modQ_eq_one_of_pow_normalizer (K : Subgroup G) (hK : Commensurated K) (x : G) {m : ℕ}
    (hm : m ≠ 0) (h : x ^ m ∈ Subgroup.normalizer (K : Set G)) : modQ K x = 1 := by sorry
