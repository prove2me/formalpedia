-- Prove2me | Theorems.Thm_PI_QmSkipWork_val_succAbove
-- name    : PI.QmSkipWork.val_succAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:55.575935+00:00
-- url     : https://prove2.me/theorems/1d6f5fe5-f744-46d1-9f37-6c89492e39d2
-- title:
--   Qm Skip Work: val succ Above
-- statement:
--   The Qm Skip Work construction uses the val succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkipSuccessorIndex/SkipSucc2.lean#L5-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkipSuccessorIndex/SkipSucc2.lean#L5-L11

import Definitions.Def_Formalism_PeriodIntegrals_QmSkip
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkipSuccessorIndex_SkipSucc2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmSkipWork

theorem PI.QmSkipWork.val_succAbove {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by sorry
