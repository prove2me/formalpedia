-- Prove2me | Theorems.Thm_PI_QnCovLinW_ofFn_prod_smul
-- name    : PI.QnCovLinW.ofFn_prod_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:14:16.242698+00:00
-- url     : https://prove2.me/theorems/ecca4bd7-e61b-47be-be22-8fc20631f523
-- title:
--   Qn Cov Lin W: of Fn prod smul
-- statement:
--   The Qn Cov Lin W construction uses the of Fn prod smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantLinearProduct/OfFnProdSmul.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantLinearProduct/OfFnProdSmul.lean#L19-L26

import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantLinearProduct_OfFnProdSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovLinW
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnCovLinW.ofFn_prod_smul {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (t : ℕ) (r : Fin t → ℂ) (x : Fin t → A),
      (List.ofFn fun k => r k • x k).prod = (∏ k, r k) • (List.ofFn x).prod
  := by sorry
