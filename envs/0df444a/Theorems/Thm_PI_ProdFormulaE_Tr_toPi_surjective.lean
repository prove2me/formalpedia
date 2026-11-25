-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Tr_toPi_surjective
-- name    : PI.ProdFormulaE.Tr.toPi_surjective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:36:52.621707+00:00
-- url     : https://prove2.me/theorems/8175cb03-05ae-4bee-b4dd-ed4671bec8e7
-- title:
--   Tr: to Pi surjective
-- statement:
--   The Tr construction uses the to Pi surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/T2SpaceOfIsValuativeTopology.lean#L115-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/T2SpaceOfIsValuativeTopology.lean#L115-L135

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_T2SpaceOfIsValuativeTopology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel Filter Topology
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F]
variable {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}

theorem PI.ProdFormulaE.Tr.toPi_surjective : TrSurj := by sorry
