-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudySmooth_contDiffAt_blockNorm_76253190e502
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudySmooth_contDiffAt_blockNorm_76253190e502
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:33.530407+00:00
-- url     : https://prove2.me/theorems/2e629e5d-8a01-4b92-827f-9ea8e8284004
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Smooth cont Diff At block Norm 76253190e502: P2 M Ground Theory Heights  Heights Fubini Study Smooth cont Diff At block Norm 76253190e502
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Smooth cont Diff At block Norm 76253190e502 construction uses the P2 M Ground Theory Heights  Heights Fubini Study Smooth cont Diff At block Norm 76253190e502 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PFsLineSmooth.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PFsLineSmooth.lean#L11-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PFsLineSmooth
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
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.FubiniStudySmooth

theorem P2M_GroundTheory_Heights__Heights_FubiniStudySmooth_contDiffAt_blockNorm_76253190e502 {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (k : K)
    (z : (Σ k, ι k) → ℂ) (hz : ∃ i, z ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => ‖WithLp.toLp 2 (fun i => w ⟨k, i⟩)‖) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudySmooth».«contDiffAt_blockNorm» := P2M_GroundTheory_Heights__Heights_FubiniStudySmooth_contDiffAt_blockNorm_76253190e502
