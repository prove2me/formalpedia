-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_relIndex_conj_right_ne_zero
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.relIndex_conj_right_ne_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:48:28.858871+00:00
-- url     : https://prove2.me/theorems/e3e06e3b-a916-51cc-b53f-68f02ec32f11
-- title:
--   Ad Index Eq: rel Index conj right ne zero
-- statement:
--   The Ad Index Eq construction uses the rel Index conj right ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ModQEqOneOfMemNormalizer.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ModQEqOneOfMemNormalizer.lean#L80-L83

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.relIndex_conj_right_ne_zero (K : Subgroup G) (hK : Commensurated K) (a : G) :
    K.relIndex (K.map (MulAut.conj a).toMonoidHom) ≠ 0 := by sorry
