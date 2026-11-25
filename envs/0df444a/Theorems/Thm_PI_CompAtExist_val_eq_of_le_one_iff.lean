-- Prove2me | Theorems.Thm_PI_CompAtExist_val_eq_of_le_one_iff
-- name    : PI.CompAtExist.val_eq_of_le_one_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:27:00.225807+00:00
-- url     : https://prove2.me/theorems/fc46afe0-3acd-4f80-9b96-3025519e4a84
-- title:
--   Comp At Exist: val eq of le one iff
-- statement:
--   The Comp At Exist construction uses the val eq of le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionExistence/LeOneIffOfMulEqOne.lean#L14-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionExistence/LeOneIffOfMulEqOne.lean#L14-L83

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CompAtExist
open NumberField IsDedekindDomain ReciprocityTheory.Aut

theorem PI.CompAtExist.val_eq_of_le_one_iff {K : Type*} [Field K] (μ ν : Valuation K (WithZero (Multiplicative ℤ)))
    (h : ∀ x, μ x ≤ 1 ↔ ν x ≤ 1) {ϖ π : K} (hϖ : ν ϖ = WithZero.exp (-1))
    (hπ : μ π = WithZero.exp (-1)) (x : K) : μ x = ν x := by sorry
