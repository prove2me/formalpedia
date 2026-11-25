-- Prove2me | Theorems.Thm_PI_WGB_chiB_weight
-- name    : PI.WGB.chiB_weight
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:05.547506+00:00
-- url     : https://prove2.me/theorems/1633ed18-8e7d-428a-afc0-4db979130597
-- title:
--   WGB: chi B weight
-- statement:
--   The WGB construction uses the chi B weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L46-L51

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial

theorem PI.WGB.chiB_weight {n : ℕ} {σ : Type*} (t : Fin n → ℂ) (w : σ → (Fin n → ℕ)) (e : σ →₀ ℕ) :
    chiB t (Finsupp.weight w e) = ∏ v ∈ e.support, chiB t (w v) ^ e v := by sorry
