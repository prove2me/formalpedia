-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_locToSemiloc_coe_05d28c336456
-- name    : P2M_GroundTheory_Heights__Heights_Inter_locToSemiloc_coe_05d28c336456
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:02.545226+00:00
-- url     : https://prove2.me/theorems/3bb1ebb4-e8bd-4d2e-825a-721a26874cde
-- title:
--   P2 M Ground Theory Heights  Heights Inter loc To Semiloc coe 05d28c336456: P2 M Ground Theory Heights  Heights Inter loc To Semiloc coe 05d28c336456
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter loc To Semiloc coe 05d28c336456 construction uses the P2 M Ground Theory Heights  Heights Inter loc To Semiloc coe 05d28c336456 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocRing.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocRing.lean#L134-L138

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IdDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_locToSemiloc_coe_05d28c336456 {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) (x : locRing (imageZ v P') W) :
    ((locToSemiloc hv P' W x : semiLocRing P' (fibreOver v P' W)) : FractionRing (MRing ι' ⧸ P')) =
      fracMapZ v P' x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«locToSemiloc_coe» := P2M_GroundTheory_Heights__Heights_Inter_locToSemiloc_coe_05d28c336456
