-- Prove2me | Theorems.Thm_PI_ProdFormulaE_HaarBox_isOpen_ball
-- name    : PI.ProdFormulaE.HaarBox.isOpen_ball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:06.773834+00:00
-- url     : https://prove2.me/theorems/5d8b9093-de5c-4850-b6e6-d588b53ef45d
-- title:
--   Haar Box: is Open ball
-- statement:
--   The Haar Box construction uses the is Open ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarBox.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarBox.lean#L30-L39

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
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}

theorem PI.ProdFormulaE.HaarBox.isOpen_ball (γ : ValueGroupWithZero K) (hγ : γ ≠ 0) :
    IsOpen {x : K | valuation K x ≤ γ} := by sorry
