-- Prove2me | Theorems.Thm_UpperTheory_f_mul_leastAdmissibleLevel_rows_le
-- name    : UpperTheory.f_mul_leastAdmissibleLevel_rows_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:49:43.075684+00:00
-- url     : https://prove2.me/theorems/5633a7cf-120e-5f99-aca4-1c4b20bd8173
-- title:
--   Upper Theory: f mul least Admissible Level rows le
-- statement:
--   The Upper Theory construction uses the f mul least Admissible Level rows le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/FMulLeastAdmissibleLevelRowsLe.lean#L39-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/FMulLeastAdmissibleLevelRowsLe.lean#L39-L76

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RestNonneg
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_FMulLeastAdmissibleLevelRowsLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds

theorem UpperTheory.f_mul_leastAdmissibleLevel_rows_le :
    ∀ (r f n m nW l k : ℕ) (L : ℝ), 1 ≤ m → m ≤ n → n ≤ r → 2 ≤ f → n + 1 = k → 3 ≤ L → Real.log k ≤ L →
    10 * (r : ℝ) * (f + (f : ℝ) ^ 2 * (n : ℝ) ^ 3 * L ^ 2 / m) ≤ nW → 5 ≤ l → f * ((RF.i0 k l + 1) * n + 4 * r) ≤ nW := by sorry
