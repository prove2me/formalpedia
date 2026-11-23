-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Frac_den_eq_one_of_norm_le_one
-- name    : PI.ProdFormulaE.Frac.den_eq_one_of_norm_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:03.993661+00:00
-- url     : https://prove2.me/theorems/2f48e06b-dd79-4bd6-90ed-419c12adb650
-- title:
--   Frac: den eq one of norm le one
-- statement:
--   The Frac construction uses the den eq one of norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/DenEqOneOfForallPadicNormLeOne.lean#L142-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/DenEqOneOfForallPadicNormLeOne.lean#L142-L161

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

theorem PI.ProdFormulaE.Frac.den_eq_one_of_norm_le_one {l : ℕ} [hl : Fact l.Prime] {a : ℚ} {n : ℕ}
    (ha : a.den = l ^ n) {T : ℚ_[l]} (hT : ‖T‖ ≤ 1) (hTa : ‖T - (a : ℚ_[l])‖ ≤ 1) :
    a.den = 1 := by sorry
