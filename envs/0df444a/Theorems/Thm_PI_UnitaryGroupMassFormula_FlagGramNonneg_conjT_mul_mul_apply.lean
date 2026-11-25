-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_conjT_mul_mul_apply
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.conjT_mul_mul_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:36.068567+00:00
-- url     : https://prove2.me/theorems/38664579-c132-5451-b1e3-4f62b2ca2e8d
-- title:
--   Flag Gram Nonneg: conj T mul mul apply
-- statement:
--   The Flag Gram Nonneg construction uses the conj T mul mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/ConjTMulMulApply.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/ConjTMulMulApply.lean#L22-L27

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_ConjTMulMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.conjT_mul_mul_apply {m n : Type} [Fintype m] (A : Matrix m n ℂ) (B : Matrix m m ℂ) (i j : n) :
    (Aᴴ * B * A) i j = star (fun k => A k i) ⬝ᵥ (B *ᵥ fun k => A k j) := by sorry
