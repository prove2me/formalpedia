-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_d_eq_zero
-- name    : ReciprocityTheory.L2DbarEstimates.F.cut_d_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:37.697272+00:00
-- url     : https://prove2.me/theorems/4073263f-c425-5708-ac97-234be2bbd6c5
-- title:
--   F: cut d eq zero
-- statement:
--   The F construction uses the cut d eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L126-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L126-L142

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
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

theorem ReciprocityTheory.L2DbarEstimates.F.cut_d_eq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (η : M → ℝ) (U : Set M) (hU : IsOpen U)
    (hη : ∀ y ∈ U, η y = 1) (x : M) (hx : x ∈ U) :
    d n z j (fun y => (η y : ℂ)) x = 0 ∧ db n z j (fun y => (η y : ℂ)) x = 0 := by sorry
