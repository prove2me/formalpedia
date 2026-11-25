-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticePointCount_det_gram_eq_sq_b3d628168b4c
-- name    : P2M_GroundTheory_Heights__Heights_LatticePointCount_det_gram_eq_sq_b3d628168b4c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:03.583863+00:00
-- url     : https://prove2.me/theorems/cc095974-36c0-4727-974e-20353ee3c687
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Point Count det gram eq sq b3d628168b4c: P2 M Ground Theory Heights  Heights Lattice Point Count det gram eq sq b3d628168b4c
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Point Count det gram eq sq b3d628168b4c construction uses the P2 M Ground Theory Heights  Heights Lattice Point Count det gram eq sq b3d628168b4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VolumeFundamentalDomainEq.lean#L85-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VolumeFundamentalDomainEq.lean#L85-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VolumeFundamentalDomainEq
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
open MeasureTheory Metric Module Submodule
open scoped ENNReal Pointwise
open GroundTheory.Heights₂.Heights.LatticePointCount

theorem P2M_GroundTheory_Heights__Heights_LatticePointCount_det_gram_eq_sq_b3d628168b4c {r : ℕ} (c : Fin r → EuclideanSpace ℝ (Fin r)) :
    (Matrix.of fun i j ↦ @inner ℝ _ _ (c i) (c j)).det =
      ((EuclideanSpace.basisFun (Fin r) ℝ).toBasis.det c) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticePointCount».«det_gram_eq_sq» := P2M_GroundTheory_Heights__Heights_LatticePointCount_det_gram_eq_sq_b3d628168b4c
