-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Frac_den_sub_sum_eq_one
-- name    : PI.ProdFormulaE.Frac.den_sub_sum_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:36:19.221991+00:00
-- url     : https://prove2.me/theorems/e32ff746-bf94-599a-8001-af2cc60b5310
-- title:
--   Frac: den sub sum eq one
-- statement:
--   The Frac construction uses the den sub sum eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/DenEqOneOfForallPadicNormLeOne.lean#L56-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/DenEqOneOfForallPadicNormLeOne.lean#L56-L80

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

theorem PI.ProdFormulaE.Frac.den_sub_sum_eq_one {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, (ℓ i).Prime) (a : ι → ℚ)
    (ha : ∀ i, ∃ n : ℕ, (a i).den = ℓ i ^ n) (fib : ℕ → Finset ι)
    (hfib : ∀ i q, i ∈ fib q ↔ ℓ i = q) (I : Finset ι) (hI : ∀ i, i ∉ I → (a i).den = 1)
    (t : ℚ) (ht : ∀ q : ℕ, q.Prime → padicNorm q (t - ∑ i ∈ fib q, a i) ≤ 1) :
    (t - ∑ i ∈ I, a i).den = 1 := by sorry
