-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSupSmall_eval_map_int_3fe0911283fe
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSupSmall_eval_map_int_3fe0911283fe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:36.434996+00:00
-- url     : https://prove2.me/theorems/2d6d6c9e-9eeb-43dc-b70b-b7845e01769c
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Sup Small eval map int 3fe0911283fe: P2 M Ground Theory Heights  Heights YPlus Sup Small eval map int 3fe0911283fe
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Sup Small eval map int 3fe0911283fe construction uses the P2 M Ground Theory Heights  Heights YPlus Sup Small eval map int 3fe0911283fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSupSmall.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSupSmall.lean#L15-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSupSmall
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSupSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_YPlusSupSmall_eval_map_int_3fe0911283fe {σ R : Type*} [CommRing R] (w : σ → R) (p : MvPolynomial σ ℤ) :
    eval w (map (Int.castRingHom R) p) = aeval w p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSupSmall».«eval_map_int» := P2M_GroundTheory_Heights__Heights_YPlusSupSmall_eval_map_int_3fe0911283fe
