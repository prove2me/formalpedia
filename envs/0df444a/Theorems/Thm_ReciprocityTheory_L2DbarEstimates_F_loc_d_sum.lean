-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_d_sum
-- name    : ReciprocityTheory.L2DbarEstimates.F.loc_d_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:55:42.099978+00:00
-- url     : https://prove2.me/theorems/29a3d008-9886-5c10-a852-1e7e71996d89
-- title:
--   F: loc d sum
-- statement:
--   The F construction uses the loc d sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L74-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L74-L94

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
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

theorem ReciprocityTheory.L2DbarEstimates.F.loc_d_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℂ) (hf : ∀ i, Ck n z 1 (f i)) (j : Fin n) (x : M) :
    d n z j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, d n z j (f i) x := by sorry
