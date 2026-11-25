-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_aesmW
-- name    : ReciprocityTheory.L2DbarEstimates.F.cut_aesmW
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:27.354339+00:00
-- url     : https://prove2.me/theorems/ed116c3c-4cd5-5f05-ba61-da12c9cf2e49
-- title:
--   F: cut aesm W
-- statement:
--   The F construction uses the cut aesm W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L371-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L371-L390

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.F.cut_aesmW {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (n : ℕ) (z : M → V n) (μ : Measure M) (ph ψ η c : M → ℝ) (f : M → V n) (w : M → ℂ)
    (hc : Continuous c) (hE : Continuous (fun x => w1 ph ψ x - w2 ph ψ x))
    (hd : ∀ j, Continuous (d n z j (fun y => (η y : ℂ))))
    (hf : AEStronglyMeasurable f μ) (hw : AEStronglyMeasurable w μ) :
    AEStronglyMeasurable (fun x => (c x : ℂ) * w x - (Real.exp (w1 ph ψ x - w2 ph ψ x) : ℂ) *
      ∑ j, d n z j (fun y => (η y : ℂ)) x * f x j) μ := by sorry
