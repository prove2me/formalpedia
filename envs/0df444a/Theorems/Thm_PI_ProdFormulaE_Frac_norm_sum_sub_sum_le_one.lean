-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Frac_norm_sum_sub_sum_le_one
-- name    : PI.ProdFormulaE.Frac.norm_sum_sub_sum_le_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:05.63451+00:00
-- url     : https://prove2.me/theorems/44b19a9b-a0b2-41a8-814a-9beedc38d2cf
-- title:
--   Frac: norm sum sub sum le one
-- statement:
--   The Frac construction uses the norm sum sub sum le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/DenEqOneOfForallPadicNormLeOne.lean#L163-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/DenEqOneOfForallPadicNormLeOne.lean#L163-L168

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

theorem PI.ProdFormulaE.Frac.norm_sum_sub_sum_le_one {q : ℕ} [Fact q.Prime] {ι : Type*} (s : Finset ι)
    (T b : ι → ℚ_[q]) (h : ∀ i ∈ s, ‖T i - b i‖ ≤ 1) :
    ‖∑ i ∈ s, T i - ∑ i ∈ s, b i‖ ≤ 1 := by sorry
