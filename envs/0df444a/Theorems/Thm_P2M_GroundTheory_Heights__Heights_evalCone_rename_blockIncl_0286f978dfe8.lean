-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_rename_blockIncl_0286f978dfe8
-- name    : P2M_GroundTheory_Heights__Heights_evalCone_rename_blockIncl_0286f978dfe8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:50:16.831154+00:00
-- url     : https://prove2.me/theorems/d6d1a5e7-97c9-5ea6-87ea-26352001123d
-- title:
--   P2 M Ground Theory Heights  Heights eval Cone rename block Incl 0286f978dfe8: P2 M Ground Theory Heights  Heights eval Cone rename block Incl 0286f978dfe8
-- statement:
--   The P2 M Ground Theory Heights  Heights eval Cone rename block Incl 0286f978dfe8 construction uses the P2 M Ground Theory Heights  Heights eval Cone rename block Incl 0286f978dfe8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VarsSubsetRangeBlockIncl.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VarsSubsetRangeBlockIncl.lean#L21-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VarsSubsetRangeBlockIncl
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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_evalCone_rename_blockIncl_0286f978dfe8 {F : Type*} [CommRing F] (k₀ : ι) (z : Cone n F)
    (f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ) :
    evalCone z (rename (blockIncl k₀) f') = evalCone (projBlock k₀ z) f' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«evalCone_rename_blockIncl» := P2M_GroundTheory_Heights__Heights_evalCone_rename_blockIncl_0286f978dfe8
