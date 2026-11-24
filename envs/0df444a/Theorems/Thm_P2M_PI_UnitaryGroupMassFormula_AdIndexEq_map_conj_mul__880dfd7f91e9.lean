-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_AdIndexEq_map_conj_mul__880dfd7f91e9
-- name    : P2M_PI_UnitaryGroupMassFormula_AdIndexEq_map_conj_mul__880dfd7f91e9
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:50:21.297413+00:00
-- url     : https://prove2.me/theorems/fcfc054e-29d8-47bc-a4e1-8fb5f984f34f
-- title:
--   P2 M PI Unitary Group Mass Formula Ad Index Eq map conj mul  880dfd7f91e9: P2 M PI Unitary Group Mass Formula Ad Index Eq map conj mul  880dfd7f91e9
-- statement:
--   The P2 M PI Unitary Group Mass Formula Ad Index Eq map conj mul  880dfd7f91e9 construction uses the P2 M PI Unitary Group Mass Formula Ad Index Eq map conj mul  880dfd7f91e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ModQEqOneOfMemNormalizer.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ModQEqOneOfMemNormalizer.lean#L60-L66

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

theorem P2M_PI_UnitaryGroupMassFormula_AdIndexEq_map_conj_mul__880dfd7f91e9 (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by sorry

alias «PI».«UnitaryGroupMassFormula».«AdIndexEq».«map_conj_mul'» := P2M_PI_UnitaryGroupMassFormula_AdIndexEq_map_conj_mul__880dfd7f91e9
