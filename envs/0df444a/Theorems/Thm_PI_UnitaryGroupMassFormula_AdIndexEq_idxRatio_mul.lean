-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_idxRatio_mul
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.idxRatio_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:38:29.368985+00:00
-- url     : https://prove2.me/theorems/bc87504d-c447-4ffa-9f88-00566eb2d6e3
-- title:
--   Ad Index Eq: idx Ratio mul
-- statement:
--   The Ad Index Eq construction uses the idx Ratio mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ModQEqOneOfMemNormalizer.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ModQEqOneOfMemNormalizer.lean#L38-L49

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.idxRatio_mul (A B C : Subgroup G)
    (hAB : B.relIndex A ≠ 0) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hBC : C.relIndex B ≠ 0) :
    idxRatio A B * idxRatio B C = idxRatio A C := by sorry
