-- Prove2me | Theorems.Thm_PI_QnCovHatW_decomp_unique
-- name    : PI.QnCovHatW.decomp_unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:36:30.555558+00:00
-- url     : https://prove2.me/theorems/ebcd7464-e968-4c4d-89cb-4f2ab2b07e9f
-- title:
--   Qn Cov Hat W: decomp unique
-- statement:
--   The Qn Cov Hat W construction uses the decomp unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/InjDecomp.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/InjDecomp.lean#L27-L37

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

theorem PI.QnCovHatW.decomp_unique {m : ℕ} {i i' : Fin (m + 1)} {σ σ' : Equiv.Perm (Fin m)}
    (h : i.succAbove ∘ σ = i'.succAbove ∘ σ') : i = i' ∧ σ = σ' := by sorry
