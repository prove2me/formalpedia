-- Prove2me | Theorems.Thm_PI_QnCovHatW_inj_decomp
-- name    : PI.QnCovHatW.inj_decomp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:36:28.509229+00:00
-- url     : https://prove2.me/theorems/ae61feea-b185-4cc6-9020-6f9d38cac54b
-- title:
--   Qn Cov Hat W: inj decomp
-- statement:
--   The Qn Cov Hat W construction uses the inj decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/InjDecomp.lean#L7-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/InjDecomp.lean#L7-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_InjDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open PI PI.QnCovHatW

theorem PI.QnCovHatW.inj_decomp {m : ℕ} (c : Fin m → Fin (m + 1)) (hc : Function.Injective c) :
    ∃ i : Fin (m + 1), ∃ σ : Equiv.Perm (Fin m), c = i.succAbove ∘ σ := by sorry
