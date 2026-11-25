-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Frac_padicNorm_sub_le_one
-- name    : PI.ProdFormulaE.Frac.padicNorm_sub_le_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:06.986822+00:00
-- url     : https://prove2.me/theorems/abf22a4c-22b9-4438-822b-3ea59766b954
-- title:
--   Frac: padic Norm sub le one
-- statement:
--   The Frac construction uses the padic Norm sub le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/DenEqOneOfForallPadicNormLeOne.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/DenEqOneOfForallPadicNormLeOne.lean#L52-L54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open PI PI.ProdFormulaE PI.ProdFormulaE.Frac

theorem PI.ProdFormulaE.Frac.padicNorm_sub_le_one {q : ℕ} [Fact q.Prime] {a b : ℚ} (ha : padicNorm q a ≤ 1)
    (hb : padicNorm q b ≤ 1) : padicNorm q (a - b) ≤ 1 := by sorry
