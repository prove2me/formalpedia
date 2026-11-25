-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_ck_sum
-- name    : ReciprocityTheory.L2DbarEstimates.F.loc_ck_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:22.430171+00:00
-- url     : https://prove2.me/theorems/ce088eb9-ba81-4a98-9eab-950cfb05f51d
-- title:
--   F: loc ck sum
-- statement:
--   The F construction uses the loc ck sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L66-L72

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
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

theorem ReciprocityTheory.L2DbarEstimates.F.loc_ck_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℂ) (hf : ∀ i, Ck n z k (f i)) :
    Ck n z k (fun x => ∑ i ∈ s, f i x) := by sorry
