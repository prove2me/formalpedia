-- Prove2me | Theorems.Thm_PI_FockWtDegWork_fockAct1_monomial
-- name    : PI.FockWtDegWork.fockAct1_monomial
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:32:09.472127+00:00
-- url     : https://prove2.me/theorems/123620d1-fd98-5c4e-91c7-4b6142431183
-- title:
--   Fock Wt Deg Work: fock Act1 monomial
-- statement:
--   The Fock Wt Deg Work construction uses the fock Act1 monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L142-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L142-L147

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

theorem PI.FockWtDegWork.fockAct1_monomial (p q r s : ℕ) (a : Ix p q) (β : Ln p q r s →₀ ℕ) :
    fockAct1 p q r s (Eab a a) (MvPolynomial.monomial β (1 : ℂ)) =
      ((W1 a β : ℚ) : ℂ) • MvPolynomial.monomial β (1 : ℂ) := by sorry
