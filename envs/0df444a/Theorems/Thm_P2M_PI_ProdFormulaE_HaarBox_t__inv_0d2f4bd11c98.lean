-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_HaarBox_t__inv_0d2f4bd11c98
-- name    : P2M_PI_ProdFormulaE_HaarBox_t__inv_0d2f4bd11c98
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:56:54.842344+00:00
-- url     : https://prove2.me/theorems/c55431c6-548f-577f-bc85-91e7b65957f7
-- title:
--   P2 M PI Prod Formula E Haar Box t  inv 0d2f4bd11c98: P2 M PI Prod Formula E Haar Box t  inv 0d2f4bd11c98
-- statement:
--   The P2 M PI Prod Formula E Haar Box t  inv 0d2f4bd11c98 construction uses the P2 M PI Prod Formula E Haar Box t  inv 0d2f4bd11c98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarTransv.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarTransv.lean#L33-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarTransv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Module Matrix
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem P2M_PI_ProdFormulaE_HaarBox_t__inv_0d2f4bd11c98 (t : Matrix.TransvectionStruct ι K) : tγ t.inv = tγ t := by sorry

alias «PI».«ProdFormulaE».«HaarBox».«tγ_inv» := P2M_PI_ProdFormulaE_HaarBox_t__inv_0d2f4bd11c98
