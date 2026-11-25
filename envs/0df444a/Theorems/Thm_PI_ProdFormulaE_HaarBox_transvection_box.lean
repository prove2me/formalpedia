-- Prove2me | Theorems.Thm_PI_ProdFormulaE_HaarBox_transvection_box
-- name    : PI.ProdFormulaE.HaarBox.transvection_box
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:34.207795+00:00
-- url     : https://prove2.me/theorems/700b2cf5-f1de-4c4c-89e9-4e8c8e9ff623
-- title:
--   Haar Box: transvection box
-- statement:
--   The Haar Box construction uses the transvection box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarTransv.lean#L74-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarTransv.lean#L74-L94

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

theorem PI.ProdFormulaE.HaarBox.transvection_box (b : Basis ι K E) (t : Matrix.TransvectionStruct ι K) :
    ∃ γ : ι → ValueGroupWithZero K, (∀ i, γ i ≠ 0) ∧
      Matrix.toLin b b t.toMatrix '' box b γ = box b γ := by sorry
