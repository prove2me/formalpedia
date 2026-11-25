-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Frac_padicNorm_le_one_of_den_pow
-- name    : PI.ProdFormulaE.Frac.padicNorm_le_one_of_den_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:53.306046+00:00
-- url     : https://prove2.me/theorems/ee2918a1-5e39-53b7-b1af-aa43b6e08925
-- title:
--   Frac: padic Norm le one of den pow
-- statement:
--   The Frac construction uses the padic Norm le one of den pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/DenEqOneOfForallPadicNormLeOne.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/DenEqOneOfForallPadicNormLeOne.lean#L31-L35

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

theorem PI.ProdFormulaE.Frac.padicNorm_le_one_of_den_pow {q l : ℕ} [hq : Fact q.Prime] (hl : l.Prime) (hne : l ≠ q)
    {a : ℚ} {n : ℕ} (ha : a.den = l ^ n) : padicNorm q a ≤ 1 := by sorry
