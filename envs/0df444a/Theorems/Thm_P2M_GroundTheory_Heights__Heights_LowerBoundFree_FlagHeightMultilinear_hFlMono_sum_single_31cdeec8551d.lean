-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_hFlMono_sum_single_31cdeec8551d
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_hFlMono_sum_single_31cdeec8551d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:05.770979+00:00
-- url     : https://prove2.me/theorems/08c723a9-e804-51d9-8716-d4eb4961b143
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear h Fl Mono sum single 31cdeec8551d: P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear h Fl Mono s
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear h Fl Mono sum single 31cdeec8551d construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear h Fl Mono sum single 31cdeec8551d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean#L181-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean#L181-L206

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
variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_hFlMono_sum_single_31cdeec8551d (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    (hP : IsArithVar (PFl Ψ N) (dimFl Ψ N + 1)) (r : Fin (dimFl Ψ N + 1) → Ψ × Fin N) :
    hFlMono Ψ N II (∑ i, Finsupp.single (r i) 1) =
      II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun i => xLine Ψ N (r i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FlagHeightMultilinear».«hFlMono_sum_single» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_hFlMono_sum_single_31cdeec8551d
