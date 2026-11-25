-- Prove2me | Theorems.Thm_PI_EF_PK_term_mul_kernel
-- name    : PI.EF.PK.term_mul_kernel
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:26.311371+00:00
-- url     : https://prove2.me/theorems/0e82449b-6470-4435-879a-86d5bc50cad5
-- title:
--   PK: term mul kernel
-- statement:
--   The PK construction uses the term mul kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronTruncOf.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronTruncOf.lean#L25-L30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real ArithmeticFunction LSeries

theorem PI.EF.PK.term_mul_kernel (a : ℕ → ℂ) (u : ℝ) (hu : 0 < u) (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    term a s n * ((u : ℂ) ^ s / s) = a n * (((u / n : ℝ) : ℂ) ^ s / s) := by sorry
