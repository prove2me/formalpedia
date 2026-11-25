-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_fsMultilin_apply_b7db3b48315c
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_fsMultilin_apply_b7db3b48315c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:39:49.047988+00:00
-- url     : https://prove2.me/theorems/83a9418b-5a18-5f0b-816f-c483a5397389
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear fs Multilin apply b7db3b48315c: P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear fs Multilin ap
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear fs Multilin apply b7db3b48315c construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear fs Multilin apply b7db3b48315c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean#L125-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean#L125-L126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PHFlProdLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_fsMultilin_apply_b7db3b48315c (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (v : Fin (n + 1) → K → ℤ) :
    fsMultilin hI hP v = I P (n + 1) (fun i => fsHerm ι (v i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FlagHeightMultilinear».«fsMultilin_apply» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_fsMultilin_apply_b7db3b48315c
