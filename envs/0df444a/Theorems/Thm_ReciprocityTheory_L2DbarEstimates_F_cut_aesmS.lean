-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_aesmS
-- name    : ReciprocityTheory.L2DbarEstimates.F.cut_aesmS
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:33.106796+00:00
-- url     : https://prove2.me/theorems/40b764e5-1a6c-4a2f-8f04-c251754cacc0
-- title:
--   F: cut aesm S
-- statement:
--   The F construction uses the cut aesm S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L392-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L392-L422

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

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

theorem ReciprocityTheory.L2DbarEstimates.F.cut_aesmS {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (n : ℕ) (z : M → V n) (μ : Measure M) (η c : M → ℝ) (f : M → V n)
    (σ : M → Fin n → Fin n → ℂ) (hc : Continuous c)
    (hd : ∀ j, Continuous (db n z j (fun y => (η y : ℂ))))
    (hf : AEStronglyMeasurable f μ) (hσ : AEStronglyMeasurable σ μ) :
    AEStronglyMeasurable (fun x => fun j k => (c x : ℂ) * σ x j k +
      wedge (fun i => db n z i (fun y => (η y : ℂ)) x) (fun i => f x i) j k) μ := by sorry
