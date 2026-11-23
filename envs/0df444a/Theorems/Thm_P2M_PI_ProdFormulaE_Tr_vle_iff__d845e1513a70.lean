-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_Tr_vle_iff__d845e1513a70
-- name    : P2M_PI_ProdFormulaE_Tr_vle_iff__d845e1513a70
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:15.197491+00:00
-- url     : https://prove2.me/theorems/fc1949ef-4d59-4def-8e21-79981f4b3a97
-- title:
--   P2 M PI Prod Formula E Tr vle iff  d845e1513a70: P2 M PI Prod Formula E Tr vle iff  d845e1513a70
-- statement:
--   The P2 M PI Prod Formula E Tr vle iff  d845e1513a70 construction uses the P2 M PI Prod Formula E Tr vle iff  d845e1513a70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/InjectiveOfLinearIndependent.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/InjectiveOfLinearIndependent.lean#L12-L14

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

theorem P2M_PI_ProdFormulaE_Tr_vle_iff__d845e1513a70 {K : Type*} [Field K] [ValuativeRel K] (x y : K) :
    x ≤ᵥ y ↔ valuation K x ≤ valuation K y := by sorry

alias «PI».«ProdFormulaE».«Tr».«vle_iff'» := P2M_PI_ProdFormulaE_Tr_vle_iff__d845e1513a70
