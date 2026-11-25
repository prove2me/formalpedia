-- Prove2me | Theorems.Thm_PI_QnCovLinW_tm_conj
-- name    : PI.QnCovLinW.tm_conj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:37:03.943817+00:00
-- url     : https://prove2.me/theorems/ba688d15-f233-5455-a434-e200c411961e
-- title:
--   Qn Cov Lin W: tm conj
-- statement:
--   The Qn Cov Lin W construction uses the tm conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantLinearProduct/OfFnProdSmul.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantLinearProduct/OfFnProdSmul.lean#L28-L41

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

theorem PI.QnCovLinW.tm_conj {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) (u : ℂ) (a b : Fin n) :
    Tm (Econj E P Q) u a b = ∑ x : Fin n × Fin n, (P x.1 a * Q b x.2) • Tm E u x.1 x.2 := by sorry
