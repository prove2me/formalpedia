-- Prove2me | Theorems.Thm_PI_FockWtDegWork_fockAct2_monomial
-- name    : PI.FockWtDegWork.fockAct2_monomial
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:32:16.29312+00:00
-- url     : https://prove2.me/theorems/b71a50d3-a7c6-543a-8bd8-915109668a03
-- title:
--   Fock Wt Deg Work: fock Act2 monomial
-- statement:
--   The Fock Wt Deg Work construction uses the fock Act2 monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L149-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L149-L154

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

theorem PI.FockWtDegWork.fockAct2_monomial (p q r s : ℕ) (c : Ix r s) (β : Ln p q r s →₀ ℕ) :
    fockAct2 p q r s (Eab c c) (MvPolynomial.monomial β (1 : ℂ)) =
      ((W2 c β : ℚ) : ℂ) • MvPolynomial.monomial β (1 : ℂ) := by sorry
