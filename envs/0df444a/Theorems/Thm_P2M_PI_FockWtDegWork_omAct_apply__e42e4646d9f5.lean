-- Prove2me | Theorems.Thm_P2M_PI_FockWtDegWork_omAct_apply__e42e4646d9f5
-- name    : P2M_PI_FockWtDegWork_omAct_apply__e42e4646d9f5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:44.961801+00:00
-- url     : https://prove2.me/theorems/cc7d9bdf-408f-4204-852d-0b9ddf5e00e4
-- title:
--   P2 M PI Fock Wt Deg Work om Act apply  e42e4646d9f5: P2 M PI Fock Wt Deg Work om Act apply  e42e4646d9f5
-- statement:
--   The P2 M PI Fock Wt Deg Work om Act apply  e42e4646d9f5 construction uses the P2 M PI Fock Wt Deg Work om Act apply  e42e4646d9f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L71-L76

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork

theorem P2M_PI_FockWtDegWork_omAct_apply__e42e4646d9f5 (p q r s : ℕ) (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s M = ∑ l, ∑ l', M l l' • omE l l' := by sorry

alias «PI».«FockWtDegWork».«omAct_apply'» := P2M_PI_FockWtDegWork_omAct_apply__e42e4646d9f5
