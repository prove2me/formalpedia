-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_Tr_LocFam_valuation__F_le_one_d2c007035a50
-- name    : P2M_PI_ProdFormulaE_Tr_LocFam_valuation__F_le_one_d2c007035a50
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:57:20.850865+00:00
-- url     : https://prove2.me/theorems/5b39280b-60bf-44ad-ae1f-490be2f31961
-- title:
--   P2 M PI Prod Formula E Tr Loc Fam valuation  F le one d2c007035a50: P2 M PI Prod Formula E Tr Loc Fam valuation  F le one d2c007035a50
-- statement:
--   The P2 M PI Prod Formula E Tr Loc Fam valuation  F le one d2c007035a50 construction uses the P2 M PI Prod Formula E Tr Loc Fam valuation  F le one d2c007035a50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/InjectiveOfLinearIndependent.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/InjectiveOfLinearIndependent.lean#L42-L45

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

theorem P2M_PI_ProdFormulaE_Tr_LocFam_valuation__F_le_one_d2c007035a50 (D : LocFam F ℓ ι) (i : ι) (x : 𝓞 F) :
    valuation (D.K i) (D.ιF i (x : F)) ≤ 1 := by sorry

alias «PI».«ProdFormulaE».«Tr».«LocFam».«valuation_ιF_le_one» := P2M_PI_ProdFormulaE_Tr_LocFam_valuation__F_le_one_d2c007035a50
