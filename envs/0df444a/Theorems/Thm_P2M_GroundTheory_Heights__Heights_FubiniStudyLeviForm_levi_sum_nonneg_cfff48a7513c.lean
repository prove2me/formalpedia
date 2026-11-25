-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLeviForm_levi_sum_nonneg_cfff48a7513c
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLeviForm_levi_sum_nonneg_cfff48a7513c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:43.075546+00:00
-- url     : https://prove2.me/theorems/9ea0769e-245a-446a-92ad-6f3d61c4536b
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Levi Form levi sum nonneg cfff48a7513c: P2 M Ground Theory Heights  Heights Fubini Study Levi Form levi sum nonneg cfff48a7513c
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Levi Form levi sum nonneg cfff48a7513c construction uses the P2 M Ground Theory Heights  Heights Fubini Study Levi Form levi sum nonneg cfff48a7513c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PFsLineLevi.lean#L16-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PFsLineLevi.lean#L16-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PFsLineLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.FubiniStudyLeviForm
variable {ι : Type} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLeviForm_levi_sum_nonneg_cfff48a7513c {K : Type} {z : ι → ℂ} (f : K → (ι → ℂ) → ℝ)
    (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (hl : ∀ k w, 0 ≤ ReciprocityTheory.AnForm.levi (f k) z w)
    (w : ι → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => ∑ k ∈ s, f k y) z ∧
      0 ≤ ReciprocityTheory.AnForm.levi (fun y => ∑ k ∈ s, f k y) z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLeviForm».«levi_sum_nonneg» := P2M_GroundTheory_Heights__Heights_FubiniStudyLeviForm_levi_sum_nonneg_cfff48a7513c
