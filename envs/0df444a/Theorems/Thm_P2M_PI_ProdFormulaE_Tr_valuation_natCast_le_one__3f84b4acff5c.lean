-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_Tr_valuation_natCast_le_one__3f84b4acff5c
-- name    : P2M_PI_ProdFormulaE_Tr_valuation_natCast_le_one__3f84b4acff5c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:57:11.402092+00:00
-- url     : https://prove2.me/theorems/d77b9255-363a-5825-84a3-2e9f4fb30b22
-- title:
--   P2 M PI Prod Formula E Tr valuation nat Cast le one  3f84b4acff5c: P2 M PI Prod Formula E Tr valuation nat Cast le one  3f84b4acff5c
-- statement:
--   The P2 M PI Prod Formula E Tr valuation nat Cast le one  3f84b4acff5c construction uses the P2 M PI Prod Formula E Tr valuation nat Cast le one  3f84b4acff5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/InjectiveOfLinearIndependent.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/InjectiveOfLinearIndependent.lean#L16-L22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ExistsEqEllMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_InjectiveOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}

theorem P2M_PI_ProdFormulaE_Tr_valuation_natCast_le_one__3f84b4acff5c {K : Type*} [Field K] [ValuativeRel K] (n : ℕ) :
    valuation K (n : K) ≤ 1 := by sorry

alias «PI».«ProdFormulaE».«Tr».«valuation_natCast_le_one'» := P2M_PI_ProdFormulaE_Tr_valuation_natCast_le_one__3f84b4acff5c
