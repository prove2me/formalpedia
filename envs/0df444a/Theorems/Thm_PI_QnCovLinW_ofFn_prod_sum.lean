-- Prove2me | Theorems.Thm_PI_QnCovLinW_ofFn_prod_sum
-- name    : PI.QnCovLinW.ofFn_prod_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:37:45.510742+00:00
-- url     : https://prove2.me/theorems/59401d4a-e5c1-4eee-8734-ab57f1335c85
-- title:
--   Qn Cov Lin W: of Fn prod sum
-- statement:
--   The Qn Cov Lin W construction uses the of Fn prod sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantLinearProduct/OfFnProdSmul.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantLinearProduct/OfFnProdSmul.lean#L9-L17

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

theorem PI.QnCovLinW.ofFn_prod_sum {A : Type*} [Semiring A] {ι : Type*} [Fintype ι] :
    ∀ (t : ℕ) (f : Fin t → ι → A),
      (List.ofFn fun k => ∑ i, f k i).prod = ∑ c : Fin t → ι, (List.ofFn fun k => f k (c k)).prod
  := by sorry
