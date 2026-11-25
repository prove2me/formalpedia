-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Tr_exists_int_approx
-- name    : PI.ProdFormulaE.Tr.exists_int_approx
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:36:14.116597+00:00
-- url     : https://prove2.me/theorems/0aa6abac-cb31-57cc-8168-1adbf68fd081
-- title:
--   Tr: exists int approx
-- statement:
--   The Tr construction uses the exists int approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ExistsEqEllMul.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ExistsEqEllMul.lean#L34-L46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ExistsEqEllMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr

theorem PI.ProdFormulaE.Tr.exists_int_approx (ℓ : ℕ) [Fact ℓ.Prime] (c : ℚ_[ℓ]) (hc : ‖c‖ ≤ 1) :
    ∃ m : ℤ, ‖(c - m) / ℓ‖ ≤ 1 := by sorry
