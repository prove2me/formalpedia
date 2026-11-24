-- Prove2me | Theorems.Thm_PI_FockWtDegWork_omE_diag_monomial
-- name    : PI.FockWtDegWork.omE_diag_monomial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:38.974973+00:00
-- url     : https://prove2.me/theorems/89be3e6a-e15c-4fe2-afaf-28feae76f095
-- title:
--   Fock Wt Deg Work: om E diag monomial
-- statement:
--   The Fock Wt Deg Work construction uses the om E diag monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L19-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L19-L69

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

theorem PI.FockWtDegWork.omE_diag_monomial {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) :
    omE l l (MvPolynomial.monomial α (1 : ℂ)) =
      ((lw l α : ℚ) : ℂ) • MvPolynomial.monomial α (1 : ℂ) := by sorry
