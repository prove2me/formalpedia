-- Prove2me | Theorems.Thm_PI_ProdFormulaE_HaarBox_transvection_mulVec
-- name    : PI.ProdFormulaE.HaarBox.transvection_mulVec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:14.088931+00:00
-- url     : https://prove2.me/theorems/8fef5d48-6540-5c55-ae3c-1ea3786fd866
-- title:
--   Haar Box: transvection mul Vec
-- statement:
--   The Haar Box construction uses the transvection mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarTransv.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarTransv.lean#L20-L28

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

theorem PI.ProdFormulaE.HaarBox.transvection_mulVec (t : Matrix.TransvectionStruct ι K) (v : ι → K) (k : ι) :
    (t.toMatrix *ᵥ v) k = v k + if k = t.i then t.c * v t.j else 0 := by sorry
