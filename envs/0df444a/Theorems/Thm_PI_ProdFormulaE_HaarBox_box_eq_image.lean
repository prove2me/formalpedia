-- Prove2me | Theorems.Thm_PI_ProdFormulaE_HaarBox_box_eq_image
-- name    : PI.ProdFormulaE.HaarBox.box_eq_image
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:18.383061+00:00
-- url     : https://prove2.me/theorems/8bacaa1f-ff63-4a0f-b556-7da6d8ac3ac1
-- title:
--   Haar Box: box eq image
-- statement:
--   The Haar Box construction uses the box eq image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarBox.lean#L69-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarBox.lean#L69-L82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PI.ProdFormulaE.HaarBox.box_eq_image (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) :
    box b γ = b.equivFun.symm '' Set.univ.pi (fun i => {a : K | valuation K a ≤ γ i}) := by sorry
