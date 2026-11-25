-- Prove2me | Theorems.Thm_PI_ProdFormulaE_HaarBox_isCompact_ball
-- name    : PI.ProdFormulaE.HaarBox.isCompact_ball
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:25.593872+00:00
-- url     : https://prove2.me/theorems/bcaaa5ba-7baf-416c-8c9b-75f6eada06b5
-- title:
--   Haar Box: is Compact ball
-- statement:
--   The Haar Box construction uses the is Compact ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarBox.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarBox.lean#L41-L42

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

theorem PI.ProdFormulaE.HaarBox.isCompact_ball (γ : ValueGroupWithZero K) : IsCompact {x : K | valuation K x ≤ γ} := by sorry
