-- Prove2me | Theorems.Thm_PI_FockWtDegWork_sum_diag_of
-- name    : PI.FockWtDegWork.sum_diag_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:30.372395+00:00
-- url     : https://prove2.me/theorems/614d52ea-5aef-4a5c-bc4a-57e9753258cf
-- title:
--   Fock Wt Deg Work: sum diag of
-- statement:
--   The Fock Wt Deg Work construction uses the sum diag of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L78-L89

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

theorem PI.FockWtDegWork.sum_diag_of {p q r s : ℕ} (M : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (g : Ln p q r s → Prop) [DecidablePred g]
    (hM : ∀ l l', M l l' = if l = l' ∧ g l then 1 else 0) :
    ∑ l, ∑ l', M l l' • omE l l' = ∑ l, if g l then omE l l else 0 := by sorry
