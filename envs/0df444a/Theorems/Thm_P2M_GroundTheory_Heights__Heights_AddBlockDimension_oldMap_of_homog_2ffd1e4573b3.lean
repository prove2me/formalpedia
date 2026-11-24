-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_of_homog_2ffd1e4573b3
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_of_homog_2ffd1e4573b3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:36.825716+00:00
-- url     : https://prove2.me/theorems/fb673cd1-1768-4c8a-aa69-47e950226747
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Dimension old Map of homog 2ffd1e4573b3: P2 M Ground Theory Heights  Heights Add Block Dimension old Map of homog 2ffd1e4573b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Dimension old Map of homog 2ffd1e4573b3 construction uses the P2 M Ground Theory Heights  Heights Add Block Dimension old Map of homog 2ffd1e4573b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L35-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicNew
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
open GroundTheory.Heights₂.Heights.AddBlockDimension
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
  (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_of_homog_2ffd1e4573b3 {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    oldMap D f = (∏ k, (X (some k) : MvPolynomial (Option ι) P.FunField) ^ δ k) * C (P.mkF f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockDimension».«oldMap_of_homog» := P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_of_homog_2ffd1e4573b3
