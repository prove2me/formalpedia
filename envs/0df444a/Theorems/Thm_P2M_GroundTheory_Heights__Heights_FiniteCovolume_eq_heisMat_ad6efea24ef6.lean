-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_heisMat_ad6efea24ef6
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_heisMat_ad6efea24ef6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:45.363394+00:00
-- url     : https://prove2.me/theorems/aa7cf4c3-f456-5535-a678-a6ffe02ddc78
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume eq heis Mat ad6efea24ef6: P2 M Ground Theory Heights  Heights Finite Covolume eq heis Mat ad6efea24ef6
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume eq heis Mat ad6efea24ef6 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume eq heis Mat ad6efea24ef6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L206-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L206-L246

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
variable {H : Matrix ι ι ℂ} {a : ι → ℂ}
variable (hH : H.IsHermitian) (ha : hForm H a a = 0)
include hH ha

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_heisMat_ad6efea24ef6 {b : ι → ℂ} (hb : hForm H b b = 0) (hab : hForm H a b = 1)
    {n : Matrix ι ι ℂ} (hn : nᴴ * H * n = H) (hna : n *ᵥ a = a)
    (hn' : ∀ z, hForm H a z = 0 → ∃ c : ℂ, n *ᵥ z = z + c • a) :
    hForm H a (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a) = 0 ∧
    hForm H b (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a) = 0 ∧
    hForm H b (n *ᵥ b - b) + starRingEnd ℂ (hForm H b (n *ᵥ b - b)) +
      hForm H (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a)
        (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a) = 0 ∧
    n = heisMat H a (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a) (hForm H b (n *ᵥ b - b)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«eq_heisMat» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_heisMat_ad6efea24ef6
