-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockSubst_eq_zero_584f1638d3d0
-- name    : P2M_GroundTheory_Heights__Heights_blockSubst_eq_zero_584f1638d3d0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:55.425983+00:00
-- url     : https://prove2.me/theorems/24768905-9232-4318-bdb8-a41ba9f5a728
-- title:
--   P2 M Ground Theory Heights  Heights block Subst eq zero 584f1638d3d0: P2 M Ground Theory Heights  Heights block Subst eq zero 584f1638d3d0
-- statement:
--   The P2 M Ground Theory Heights  Heights block Subst eq zero 584f1638d3d0 construction uses the P2 M Ground Theory Heights  Heights block Subst eq zero 584f1638d3d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L119-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L119-L124

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)

theorem P2M_GroundTheory_Heights__Heights_blockSubst_eq_zero_584f1638d3d0 {f : MvPolynomial (Coord (blockAddData n k₀).extSizes) ℤ}
    (hf : f ∈ (blockAddData n k₀).extIdeal) : blockSubst n k₀ f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«blockSubst_eq_zero» := P2M_GroundTheory_Heights__Heights_blockSubst_eq_zero_584f1638d3d0
