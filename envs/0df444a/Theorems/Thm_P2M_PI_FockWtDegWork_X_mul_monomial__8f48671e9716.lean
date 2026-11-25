-- Prove2me | Theorems.Thm_P2M_PI_FockWtDegWork_X_mul_monomial__8f48671e9716
-- name    : P2M_PI_FockWtDegWork_X_mul_monomial__8f48671e9716
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:56:08.66623+00:00
-- url     : https://prove2.me/theorems/12ee1d8c-cec8-5017-a3d6-ccc8c7bf00c7
-- title:
--   P2 M PI Fock Wt Deg Work X mul monomial  8f48671e9716: P2 M PI Fock Wt Deg Work X mul monomial  8f48671e9716
-- statement:
--   The P2 M PI Fock Wt Deg Work X mul monomial  8f48671e9716 construction uses the P2 M PI Fock Wt Deg Work X mul monomial  8f48671e9716 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L12-L17

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

theorem P2M_PI_FockWtDegWork_X_mul_monomial__8f48671e9716 {σ : Type*} (l : σ) (β : σ →₀ ℕ) (c : ℂ) :
    MvPolynomial.X l * MvPolynomial.monomial β c =
      MvPolynomial.monomial (Finsupp.single l 1 + β) c := by sorry

alias «PI».«FockWtDegWork».«X_mul_monomial'» := P2M_PI_FockWtDegWork_X_mul_monomial__8f48671e9716
