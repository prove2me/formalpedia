-- Prove2me | Theorems.Thm_PI_ProdFormulaE_HaarBox_image_toLin
-- name    : PI.ProdFormulaE.HaarBox.image_toLin
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:34.075905+00:00
-- url     : https://prove2.me/theorems/cef1a65b-37f8-453b-b3a0-cf8b0115a719
-- title:
--   Haar Box: image to Lin
-- statement:
--   The Haar Box construction uses the image to Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarMain.lean#L114-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarMain.lean#L114-L130

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure ValuativeRel Topology Module
open scoped NNReal ENNReal Pointwise
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace E] [BorelSpace E]

theorem PI.ProdFormulaE.HaarBox.image_toLin (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (htrans : TransvBox b)
    (A : Matrix ι ι K) (hA : A.det ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b A '' S) = ENNReal.ofReal (modF K A.det) * μ S := by sorry
