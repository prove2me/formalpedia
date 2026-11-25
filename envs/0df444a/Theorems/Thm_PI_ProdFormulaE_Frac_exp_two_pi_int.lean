-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Frac_exp_two_pi_int
-- name    : PI.ProdFormulaE.Frac.exp_two_pi_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:36:34.441805+00:00
-- url     : https://prove2.me/theorems/a1d3fe83-578f-482d-9121-2cd0105b2ce7
-- title:
--   Frac: exp two pi int
-- statement:
--   The Frac construction uses the exp two pi int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/DenEqOneOfForallPadicNormLeOne.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/DenEqOneOfForallPadicNormLeOne.lean#L82-L84

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

theorem PI.ProdFormulaE.Frac.exp_two_pi_int (n : ℤ) : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by sorry
